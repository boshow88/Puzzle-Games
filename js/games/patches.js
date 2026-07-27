/**
 * Patches — gameplay + SVG rendering.
 *
 * Consumes puzzles from `window.PuzzleGenerators.patches(size, difficulty,
 * seed, onProgress)` and depends only on window.PuzzleCommon.
 *
 * P1 scope: render the clue board and a Reveal overlay of the solved
 * partition, so the generator can be eyeballed end-to-end. The drag-to-
 * draw interaction, conflict flagging, hints, undo and share land in later
 * passes; the render layers below are already arranged to receive them.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // Exposes game internals on window for the trace/demo tooling and
    // headless tests. Off unless ?patches_debug=1.  [DEBUG-HOOK]
    const DEBUG = typeof location !== 'undefined'
        && /[?&]patches_debug=1\b/.test(location.search);

    // ?patches_demo=conflict auto-places a deliberately wrong rectangle so
    // the violation UI can be seen (and screenshotted) immediately.  [DEBUG-HOOK]
    const DEMO = (function () {
        if (typeof location === 'undefined') return null;
        const m = /[?&]patches_demo=([a-z0-9]+)/.exec(location.search);
        return m ? m[1] : null;
    })();

    const BOARD_SIZE = 480;
    const MIN_SIZE = 5;
    const MAX_SIZE = 12;

    // Grace period after a placement before its rule violations are flagged,
    // so actively editing the board doesn't nag mid-gesture (matches Queens).
    const VIOLATION_DELAY_MS = 800;

    const SQUARE = 'square';
    const WIDE = 'wide';
    const TALL = 'tall';
    const ANY = 'any';

    // Soft, distinguishable palette so adjacent rectangles read apart.
    // Warm-leaning to sit under the red theme without clashing.
    const PATCH_COLORS = [
        '#e5737d', '#e8a15c', '#e6c65b', '#8fc07a',
        '#5cb8a8', '#6aa9e0', '#8f8fe0', '#c684cf',
        '#d98ca6', '#c9925f', '#a6bf6a', '#5fbf9e',
        '#6f9fd8', '#a58fd8', '#d484b0', '#d09090',
    ];

    function clueColor(i) {
        return PATCH_COLORS[((i % PATCH_COLORS.length) + PATCH_COLORS.length)
            % PATCH_COLORS.length];
    }

    // Matches CSS --accent-danger; used so a flagged rectangle's size badge
    // turns red along with the rectangle.
    const DANGER_HEX = '#dc3545';

    // -----------------------------------------------------------------
    // Generation wrapper (adapts the async generator to the shared
    // determinate progress bar — mirrors the other games).
    // -----------------------------------------------------------------

    async function generatePuzzle(size, difficulty, seed) {
        const progress = PC.progress;
        const onProgress = progress
            ? async (fraction) => {
                progress.setFraction(fraction);
                await progress.waitNextPaint();
            }
            : null;
        return window.PuzzleGenerators.patches(size, difficulty, seed, onProgress);
    }

    // -----------------------------------------------------------------
    // State
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        placements: [],   // player rectangles; { r, c, w, h, clue }
        won: false,
        // Active pointer gesture. A gesture that never leaves its start cell
        // is a "click" (delete); one that moves is a "drag". Starting inside a
        // placed rectangle picks it up to expand (editClue = that clue, box
        // seeded to its bounds); otherwise it draws a fresh rectangle.
        drag: null,       // { pointerId, sr, sc, minR, maxR, minC, maxC, moved, editClue }
        violationTimer: null,
        violationsShown: false,
        hint: null,       // current hint descriptor, or null when hidden
    };

    let shell = null;
    let board = null;
    let hintBanner = null;
    let clueAt = null;    // Map "r,c" -> clue index, rebuilt per puzzle
    let undoHistory = null;

    // ----- Shared-puzzle URL (seed round-trips through ?size&difficulty&seed) -----
    const VALID_SIZES = new Set([5, 6, 7, 8, 9, 10, 11, 12]);
    const VALID_DIFFS = new Set(['easy', 'medium', 'hard']);

    // Each field applies on its own — a bare ?diff=hard or ?size=10 (e.g. for a
    // ?patches_demo=orphan URL) sets that control without needing a seed too.
    function readUrlInitial() {
        if (!PC.share) return null;
        const raw = PC.share.readParams();
        const size = VALID_SIZES.has(raw.size) ? raw.size : null;
        const difficulty = VALID_DIFFS.has(raw.difficulty) ? raw.difficulty : null;
        const seed = Number.isInteger(raw.seed) ? raw.seed : null;
        if (size == null && difficulty == null && seed == null) return null;
        return { size, difficulty, seed };
    }

    const urlInitial = readUrlInitial();
    let pendingSeed = urlInitial ? urlInitial.seed : null;

    function resetPlacements() {
        state.placements = [];
        state.won = false;
        state.drag = null;
        if (state.violationTimer) {
            clearTimeout(state.violationTimer);
            state.violationTimer = null;
        }
    }

    function rebuildIndices() {
        clueAt = new Map();
        state.puzzle.clues.forEach((cl, i) => clueAt.set(cl.r + ',' + cl.c, i));
    }

    function clueIndexAt(r, c) {
        const v = clueAt.get(r + ',' + c);
        return v == null ? -1 : v;
    }

    /** Clue cells falling inside an inclusive bounding box. */
    function cluesInBox(minR, minC, maxR, maxC) {
        let count = 0;
        let idx = -1;
        state.puzzle.clues.forEach((cl, i) => {
            if (cl.r >= minR && cl.r <= maxR && cl.c >= minC && cl.c <= maxC) {
                count += 1;
                idx = i;
            }
        });
        return { count, idx };
    }

    function shapeOK(shape, w, h) {
        if (w * h < 2) return false;
        if (shape === SQUARE) return w === h;
        if (shape === WIDE) return w > h;
        if (shape === TALL) return h > w;
        return true; // any
    }

    function rectContainsCell(rc, r, c) {
        return r >= rc.r && r < rc.r + rc.h && c >= rc.c && c < rc.c + rc.w;
    }

    function rectsOverlap(a, b) {
        return a.c < b.c + b.w && b.c < a.c + a.w
            && a.r < b.r + b.h && b.r < a.r + a.h;
    }

    // -----------------------------------------------------------------
    // Undo (bounded snapshot history — one gesture = one step).
    // -----------------------------------------------------------------

    function clonePlacements(list) { return list.map((rc) => Object.assign({}, rc)); }

    function snapshotState() { return { placements: clonePlacements(state.placements) }; }

    function restoreSnapshot(snap) {
        const wasWon = state.won;
        state.placements = clonePlacements(snap.placements);
        state.won = false;
        if (wasWon) shell.clearWin(); // reverse win chrome, resume the clock
        clearHint();
        clearViolationDisplay();
        repaintRects();
        scheduleViolations();
        updateStatusRow();
    }

    function pushUndo() {
        if (!undoHistory || state.won) return;
        undoHistory.push();
        updateUndoButton();
    }

    // Undo stays available after winning (to review the last moves); it's
    // only cleared on Reset-after-win / New Game.
    function doUndo() {
        if (!state.puzzle) return;
        if (undoHistory && undoHistory.undo()) updateUndoButton();
    }

    function updateUndoButton() {
        const btn = document.getElementById('undo-btn');
        if (btn) btn.disabled = !(undoHistory && undoHistory.canUndo());
    }

    function placementIndexUnder(r, c) {
        for (let i = state.placements.length - 1; i >= 0; i--) {
            if (rectContainsCell(state.placements[i], r, c)) return i;
        }
        return -1;
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    function cellSize() {
        return BOARD_SIZE / state.puzzle.size;
    }

    function renderBoard() {
        const p = state.puzzle;
        const N = p.size;
        const cs = BOARD_SIZE / N;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        // Layer: cell backgrounds.
        const bg = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                bg.appendChild(PC.svgEl('rect', {
                    class: 'cell-bg',
                    x: c * cs, y: r * cs, width: cs, height: cs,
                    fill: '#ffffff',
                    // The grid is drawn once, by the dedicated .grid-line layer
                    // above the patches; suppress cell-bg's shared stroke so
                    // there's a single grid source that fades cleanly on win.
                    style: 'stroke: none',
                }));
            }
        }
        svg.appendChild(bg);

        // Layer: reveal / placed rectangles (below thin grid + clues).
        const rectsLayer = PC.svgEl('g', { class: 'patch-rects' });
        rectsLayer.setAttribute('id', 'patch-rects');
        svg.appendChild(rectsLayer);

        // Layer: thin interior grid lines.
        const grid = PC.svgEl('g', { class: 'grid' });
        for (let i = 1; i < N; i++) {
            grid.appendChild(PC.svgEl('line', {
                class: 'grid-line',
                x1: i * cs, y1: 0, x2: i * cs, y2: N * cs,
            }));
            grid.appendChild(PC.svgEl('line', {
                class: 'grid-line',
                x1: 0, y1: i * cs, x2: N * cs, y2: i * cs,
            }));
        }
        svg.appendChild(grid);

        // Layer: size badges (above the grid so they can mask a grid line).
        const sizes = PC.svgEl('g', { class: 'patch-sizes-layer' });
        sizes.setAttribute('id', 'patch-sizes');
        svg.appendChild(sizes);

        // Layer: outer frame.
        const borders = PC.svgEl('g', { class: 'region-borders' });
        const W = N * cs;
        for (const [x1, y1, x2, y2] of [
            [0, 0, W, 0], [0, W, W, W], [0, 0, 0, W], [W, 0, W, W],
        ]) {
            borders.appendChild(PC.svgEl('line', {
                class: 'region-border', x1, y1, x2, y2,
            }));
        }
        svg.appendChild(borders);

        // Layer: live drag preview (above the grid, below the clue glyphs
        // so a clue number stays readable through the tint).
        const preview = PC.svgEl('g', { class: 'patch-preview-layer' });
        preview.setAttribute('id', 'patch-preview');
        svg.appendChild(preview);

        // Layer: clue glyphs.
        const clues = PC.svgEl('g', { class: 'clues' });
        clues.setAttribute('id', 'clues');
        svg.appendChild(clues);

        // Layer: hint spotlight (dims non-focus cells — above the clues so
        // unrelated clue glyphs dim too — plus the focus outline).
        const hint = PC.svgEl('g', { class: 'hint-layer' });
        hint.setAttribute('id', 'hint');
        svg.appendChild(hint);

        // Layer: violation message bubbles (topmost).
        const bubbles = PC.svgEl('g', { class: 'patch-bubbles-layer' });
        bubbles.setAttribute('id', 'patch-bubbles');
        svg.appendChild(bubbles);

        repaintRects();
        repaintClues();
    }

    function repaintPreview() {
        const layer = board.querySelector('#patch-preview');
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const d = state.drag;
        if (!d) return;
        const cs = cellSize();
        const inset = Math.max(2, cs * 0.06);
        const radius = Math.max(3, cs * 0.10);
        const { count, idx } = cluesInBox(d.minR, d.minC, d.maxR, d.maxC);
        const tinted = count === 1;
        const color = tinted ? clueColor(idx) : '#7a7a7a';
        const w = d.maxC - d.minC + 1;
        const h = d.maxR - d.minR + 1;
        layer.appendChild(PC.svgEl('rect', {
            class: 'patch-preview' + (tinted ? ' tinted' : ''),
            x: d.minC * cs + inset,
            y: d.minR * cs + inset,
            width: w * cs - inset * 2,
            height: h * cs - inset * 2,
            rx: radius, ry: radius,
            fill: color, stroke: color,
        }));
        // Live size readout while dragging (matches the placed-rect badge).
        if (w * h >= 2) {
            drawSizeBadge(layer, { r: d.minR, c: d.minC, w, h }, w * h, color,
                tinted ? 0.5 : 0.34, tinted ? state.puzzle.clues[idx] : null);
        }
    }

    /** Draw the solution partition when Reveal is on (P2 will also draw
     *  the player's own placements here). */
    function repaintRects() {
        const p = state.puzzle;
        const cs = cellSize();
        const layer = board.querySelector('#patch-rects');
        while (layer.firstChild) layer.removeChild(layer.firstChild);

        const showSolution = shell.revealed && !state.won;
        const rects = showSolution ? p.solution : state.placements;
        const won = state.won;
        // On win the patches close their gaps and deepen in colour — the quilt
        // reads as finished, clearly distinct from the gapped in-play state.
        // The inset is half the 2.5 stroke so each patch's OUTER edge lands
        // exactly on the cell boundary: neighbours' borders meet flush without
        // overlapping. The grey grid lines fade out (see .board-svg.board-won).
        const inset = won ? 1.25 : Math.max(2, cs * 0.06);
        const radius = won ? 0 : Math.max(3, cs * 0.10);
        board.classList.toggle('board-won', won);

        for (const rc of rects) {
            const color = clueColor(rc.clue);
            layer.appendChild(PC.svgEl('rect', {
                class: 'patch-rect' + (showSolution ? ' reveal' : '') + (won ? ' won' : ''),
                'data-clue': rc.clue,
                x: rc.c * cs + inset,
                y: rc.r * cs + inset,
                width: rc.w * cs - inset * 2,
                height: rc.h * cs - inset * 2,
                rx: radius, ry: radius,
                fill: color,
                stroke: color,
            }));
        }

        repaintSizes();
    }

    /** Size badges: each placed rectangle's current cell-count. Shown only
     *  while actively playing (not on the reveal overlay, and gone on the
     *  finished-quilt win state). A rectangle currently flagged as a
     *  violation (red pulsing) gets a red badge to match. */
    function repaintSizes() {
        const sizeLayer = board && board.querySelector('#patch-sizes');
        if (!sizeLayer) return;
        while (sizeLayer.firstChild) sizeLayer.removeChild(sizeLayer.firstChild);
        if (!state.puzzle || state.won || shell.revealed) return;
        const violating = new Set();
        board.querySelectorAll('.patch-rect.violation').forEach((el) => {
            violating.add(parseInt(el.getAttribute('data-clue'), 10));
        });
        for (const rc of state.placements) {
            const colorHex = violating.has(rc.clue) ? DANGER_HEX : clueColor(rc.clue);
            drawSizeBadge(sizeLayer, rc, rc.w * rc.h, colorHex, 0.55,
                state.puzzle.clues[rc.clue]);
        }
    }

    /** The opaque colour a `hex` fill of the given `alpha` resolves to over
     *  the white board — so a badge matches a translucent patch/preview
     *  exactly while still masking the grid line beneath it. */
    function compositeOverWhite(hex, alpha) {
        let h = String(hex).replace('#', '');
        if (h.length === 3) h = h.split('').map((ch) => ch + ch).join('');
        const r = parseInt(h.slice(0, 2), 16);
        const g = parseInt(h.slice(2, 4), 16);
        const b = parseInt(h.slice(4, 6), 16);
        const mix = (c) => Math.round(alpha * c + (1 - alpha) * 255);
        return `rgb(${mix(r)}, ${mix(g)}, ${mix(b)})`;
    }

    /** Size badge for a box — a placed rectangle OR the live drag preview.
     *  The frame is the box's own on-white colour (opaque, so it masks the
     *  grid); the number is the saturated base colour (same family, readable —
     *  not white). Dodges one cell if its centre lands on `dodgeClue`. */
    function drawSizeBadge(layer, box, num, colorHex, alpha, dodgeClue) {
        const cs = cellSize();
        let bx = (box.c + box.w / 2) * cs;
        let by = (box.r + box.h / 2) * cs;
        if (dodgeClue) {
            const clcx = (dodgeClue.c + 0.5) * cs;
            const clcy = (dodgeClue.r + 0.5) * cs;
            if (Math.abs(bx - clcx) < cs * 0.5 && Math.abs(by - clcy) < cs * 0.5) {
                if (box.w > 1) {
                    const right = (box.c + box.w - 1) - dodgeClue.c;
                    const left = dodgeClue.c - box.c;
                    bx += (right >= left ? 1 : -1) * cs;
                } else {
                    const down = (box.r + box.h - 1) - dodgeClue.r;
                    const up = dodgeClue.r - box.r;
                    by += (down >= up ? 1 : -1) * cs;
                }
            }
        }
        const digits = String(num).length;
        const bh = cs * 0.26;
        const bw = Math.max(bh, cs * (0.12 + 0.11 * digits));
        const rx = bh * 0.42;
        layer.appendChild(PC.svgEl('rect', {
            class: 'patch-size',
            x: bx - bw / 2, y: by - bh / 2, width: bw, height: bh,
            rx, ry: rx, fill: compositeOverWhite(colorHex, alpha),
        }));
        const text = PC.svgEl('text', {
            class: 'patch-size-num',
            x: bx, y: by,
            'text-anchor': 'middle', 'dominant-baseline': 'middle',
            dy: '0.08em', 'font-size': cs * 0.18, fill: colorHex,
        });
        text.textContent = String(num);
        layer.appendChild(text);
    }

    function repaintClues() {
        const p = state.puzzle;
        const cs = cellSize();
        const layer = board.querySelector('#clues');
        while (layer.firstChild) layer.removeChild(layer.firstChild);

        p.clues.forEach((clue, i) => {
            const cx = clue.c * cs + cs / 2;
            const cy = clue.r * cs + cs / 2;
            drawClueGlyph(layer, cx, cy, cs, clue, clueColor(i));
        });
    }

    /** A clue marker: a shape swatch tinted with the clue's colour, with
     *  the size number in white when present. 'any' is drawn as a dashed
     *  wide+tall pair, per the spec. */
    function drawClueGlyph(layer, cx, cy, cs, clue, color) {
        const g = PC.svgEl('g', { class: 'clue-glyph' });
        const unit = cs * 0.74;          // long side of a wide/tall swatch (longer)
        const shortSide = cs * 0.48;     // chunky short side (kept as-is)
        const squareSide = cs * 0.58;    // a touch shorter than the long side
        const rx = Math.max(2, cs * 0.06);

        function swatch(w, h, extra) {
            return PC.svgEl('rect', Object.assign({
                class: 'clue-swatch',
                x: cx - w / 2, y: cy - h / 2, width: w, height: h,
                rx, ry: rx, fill: color,
            }, extra || {}));
        }

        if (clue.shape === SQUARE) {
            g.appendChild(swatch(squareSide, squareSide));
        } else if (clue.shape === WIDE) {
            g.appendChild(swatch(unit, shortSide));
        } else if (clue.shape === TALL) {
            g.appendChild(swatch(shortSide, unit));
        } else {
            // any → overlapping dashed wide + tall, translucent, finer dash.
            const dash = `${Math.max(1.5, cs * 0.04)} ${Math.max(1.5, cs * 0.03)}`;
            g.appendChild(swatch(unit, shortSide, {
                class: 'clue-swatch any', fill: color,
                'fill-opacity': 0.28, stroke: color, 'stroke-dasharray': dash,
            }));
            g.appendChild(swatch(shortSide, unit, {
                class: 'clue-swatch any', fill: color,
                'fill-opacity': 0.28, stroke: color, 'stroke-dasharray': dash,
            }));
        }

        if (clue.size != null) {
            const text = PC.svgEl('text', {
                class: 'clue-num',
                x: cx, y: cy,
                'text-anchor': 'middle',
                'dominant-baseline': 'middle',
                dy: '0.08em',
                'font-size': Math.max(12, cs * 0.36),
            });
            text.textContent = String(clue.size);
            g.appendChild(text);
        }
        layer.appendChild(g);
    }

    function updateStatusRow() {
        shell.setWin(state.won);
    }

    // -----------------------------------------------------------------
    // Win check
    // -----------------------------------------------------------------

    /** Solved when every clue owns exactly one placed rectangle, each
     *  rectangle satisfies its clue, they don't overlap, and together they
     *  fill the grid. One-clue-per-rectangle is already guaranteed at
     *  placement time (the drag can never enclose two clues). */
    function isWin() {
        const p = state.puzzle;
        const N = p.size;
        if (state.placements.length !== p.clues.length) return false;

        const seenClue = new Set();
        const cover = new Int8Array(N * N);
        for (const rc of state.placements) {
            if (rc.clue < 0 || seenClue.has(rc.clue)) return false;
            seenClue.add(rc.clue);
            const cl = p.clues[rc.clue];
            if (!shapeOK(cl.shape, rc.w, rc.h)) return false;
            if (cl.size != null && rc.w * rc.h !== cl.size) return false;
            for (let r = rc.r; r < rc.r + rc.h; r++) {
                for (let c = rc.c; c < rc.c + rc.w; c++) {
                    const k = r * N + c;
                    if (cover[k]) return false; // overlap
                    cover[k] = 1;
                }
            }
        }
        for (let k = 0; k < N * N; k++) if (!cover[k]) return false;
        return true;
    }

    function commitChange() {
        clearHint(); // any board change invalidates the shown hint
        repaintRects();
        if (!state.won && isWin()) {
            state.won = true;
            shell.markSolved();
            repaintRects();
        }
        updateStatusRow();
        if (state.won) clearViolationDisplay();
        else scheduleViolations();
        updateUndoButton();
    }

    // -----------------------------------------------------------------
    // Violation flagging (delayed, matches the other games' rhythm)
    // -----------------------------------------------------------------

    /** Placed rectangles that break their clue's shape or size. Overlaps
     *  can't happen (prevented during the drag), so those two are the only
     *  possible rule breaks. */
    function findViolations() {
        const p = state.puzzle;
        const N = p.size;
        const out = [];
        for (const rc of state.placements) {
            const cl = p.clues[rc.clue];
            const area = rc.w * rc.h;
            // Number: only a violation once the count EXCEEDS the target — a
            // still-too-small patch may just be mid-expansion. Judged on its
            // own, independent of shape.
            if (cl.size != null && area > cl.size) {
                out.push({ rc, msgKey: 'patchesConflictSizeOver', msgArgs: [cl.size] });
                continue;
            }
            // Shape: a wrong *current* shape is fine while the patch can still
            // grow into the target shape. It's only a violation once that's
            // impossible — blocked purely by the board edge and OTHER clue
            // cells (other placed rectangles are ignored, and the number is
            // irrelevant here).
            if (cl.shape !== ANY && !shapeOK(cl.shape, rc.w, rc.h)
                && !canReachShape(rc, rc.clue, cl.shape, N, p.clues)) {
                const key = cl.shape === SQUARE ? 'patchesConflictShapeSquare'
                    : cl.shape === WIDE ? 'patchesConflictShapeWide'
                        : 'patchesConflictShapeTall';
                out.push({ rc, msgKey: key, msgArgs: [] });
            }
        }
        return out;
    }

    /** Could `rc` still be grown (its bounding box only ever expands) into a
     *  rectangle of the target shape? Blocked only by the board edge and
     *  OTHER clue cells; other placed rectangles and the target number are
     *  deliberately ignored (shape is judged on its own). */
    function canReachShape(rc, ownIdx, shape, N, clues) {
        if (shape === ANY) return true;
        const rBot = rc.r + rc.h - 1;
        const cRight = rc.c + rc.w - 1;
        for (let r1 = 0; r1 <= rc.r; r1++) {
            for (let r2 = rBot; r2 < N; r2++) {
                for (let c1 = 0; c1 <= rc.c; c1++) {
                    for (let c2 = cRight; c2 < N; c2++) {
                        if (!shapeOK(shape, c2 - c1 + 1, r2 - r1 + 1)) continue;
                        if (boxHasForeignClue(r1, c1, r2, c2, ownIdx, clues)) continue;
                        return true;
                    }
                }
            }
        }
        return false;
    }

    function boxHasForeignClue(r1, c1, r2, c2, ownIdx, clues) {
        for (let i = 0; i < clues.length; i++) {
            if (i === ownIdx) continue;
            const cl = clues[i];
            if (cl.r >= r1 && cl.r <= r2 && cl.c >= c1 && cl.c <= c2) return true;
        }
        return false;
    }

    function scheduleViolations() {
        clearViolationDisplay();
        if (state.won || shell.revealed || !state.placements.length) return;
        state.violationTimer = setTimeout(showViolations, VIOLATION_DELAY_MS);
    }

    function showViolations() {
        state.violationTimer = null;
        if (state.won || shell.revealed) return;
        const vs = findViolations();
        for (const v of vs) {
            const el = board.querySelector(
                `.patch-rect[data-clue="${v.rc.clue}"]`);
            if (el) el.classList.add('violation');
        }
        renderBubbles(vs);
        shell.setViolationCount(vs.length);
        state.violationsShown = vs.length > 0;
        repaintSizes(); // recolour flagged rectangles' badges red
    }

    function renderBubbles(vs) {
        const layer = board.querySelector('#patch-bubbles');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const cs = cellSize();
        const bw = 210;
        const bh = 58;
        for (const v of vs) {
            const rc = v.rc;
            const cx = (rc.c + rc.w / 2) * cs;
            const x = PC.clamp(cx - bw / 2, 2, BOARD_SIZE - bw - 2);
            let y = rc.r * cs - bh - 4;
            if (y < 0) y = (rc.r + rc.h) * cs + 4;
            const fo = PC.svgEl('foreignObject', {
                x, y, width: bw, height: bh, class: 'patch-bubble-fo',
            });
            const div = document.createElementNS(
                'http://www.w3.org/1999/xhtml', 'div');
            div.setAttribute('class', 'patch-bubble');
            div.textContent = PC.i18n.t(v.msgKey, ...(v.msgArgs || []));
            fo.appendChild(div);
            layer.appendChild(fo);
        }
    }

    function clearViolationDisplay() {
        if (state.violationTimer) {
            clearTimeout(state.violationTimer);
            state.violationTimer = null;
        }
        if (!board) return;
        const layer = board.querySelector('#patch-bubbles');
        if (layer) while (layer.firstChild) layer.removeChild(layer.firstChild);
        board.querySelectorAll('.patch-rect.violation')
            .forEach((el) => el.classList.remove('violation'));
        if (shell) shell.setViolationCount(0);
        state.violationsShown = false;
        repaintSizes(); // restore badges to their clue colours
    }

    // -----------------------------------------------------------------
    // Hints — conflict-first, then the three deduction tiers.
    //   conflict : a placed rectangle already breaks its clue's rule.
    //   wrong    : a rule-valid rectangle that isn't the solution's.
    //   tier 1   : a clue whose rectangle is now forced only *because* of
    //              the cells the player has already locked in.
    //   tier 2   : a clue with a single valid placement intrinsically
    //              (every other placement would hit another clue).
    //   tier 3   : an empty cell only one clue's region can reach.
    // -----------------------------------------------------------------

    function onHint() {
        if (!state.puzzle || state.won) return;
        if (state.hint) { clearHint(); return; } // toggle off
        const h = computeHint();
        state.hint = h;
        repaintHint();
        setHintBanner(hintText(h));
    }

    /** Resolve a hint's message from its i18n key at call time, so a live
     *  language switch re-renders it (see onLocaleChange). */
    function hintText(h) {
        if (!h || !h.msgKey) return '';
        return PC.i18n.t(h.msgKey, ...(h.msgArgs || []));
    }

    // Re-render locale-dependent overlays when the language toggles.
    function onLocaleChange() {
        if (!state.puzzle) return;
        if (state.hint) setHintBanner(hintText(state.hint));
        if (state.violationsShown) showViolations();
    }

    function clearHint() {
        state.hint = null;
        const layer = board && board.querySelector('#hint');
        if (layer) while (layer.firstChild) layer.removeChild(layer.firstChild);
        setHintBanner(null);
    }

    function setHintBanner(text) {
        if (!hintBanner) return;
        hintBanner.textContent = text || '';
        hintBanner.hidden = !text;
    }

    function computeHint() {
        // 1) Rule violations take priority (conflict-first).
        const vs = findViolations();
        if (vs.length) {
            return {
                kind: 'conflict', rc: vs[0].rc, clue: vs[0].rc.clue,
                msgKey: vs[0].msgKey, msgArgs: vs[0].msgArgs,
            };
        }
        // 2) Rule-valid rectangles that don't match the unique solution.
        //    Show ALL of them at once (not one at a time) so the player can
        //    clear every dead placement in one pass.
        const wrong = findWrongPlacements();
        if (wrong.length) {
            return {
                kind: 'wrong', rc: wrong[0], rcs: wrong, clue: wrong[0].clue,
                msgKey: wrong.length > 1 ? 'patchesHintWrongMulti' : 'patchesHintWrong',
            };
        }
        // 3) The next logical deduction.
        return computeDeduction() || { kind: 'none', msgKey: 'patchesHintNone' };
    }

    function findWrongPlacements() {
        const sol = new Map();
        for (const s of state.puzzle.solution) sol.set(s.clue, s);
        const wrong = [];
        for (const rc of state.placements) {
            const s = sol.get(rc.clue);
            // Wrong only if it strays OUTSIDE its clue's solution rectangle.
            // A rectangle fully inside is a valid partial that can still be
            // expanded to the solution — a hint guides its completion instead.
            if (!s || rc.r < s.r || rc.c < s.c
                || rc.r + rc.h > s.r + s.h || rc.c + rc.w > s.c + s.w) wrong.push(rc);
        }
        return wrong;
    }

    function computeDeduction() {
        const p = state.puzzle;
        const N = p.size;
        const PI = window.PuzzleGenerators.patchesInternals;
        const tech = PI.TECHNIQUES_BY_DIFFICULTY[p.difficulty]
            || PI.TECHNIQUES_BY_DIFFICULTY.medium;

        // The player's rectangles are LOWER BOUNDS (a patch may still grow).
        // Hand them to the SHARED solver and ask for the single next deduction
        // it would make at THIS difficulty's technique level, so hints match
        // the generator exactly and harder boards (which need core/orphan
        // reasoning) always have a next step to show. No solution peeking —
        // every step is sound pure logic.
        const seed = state.placements.map((rc) => ({
            r: rc.r, c: rc.c, w: rc.w, h: rc.h, clue: rc.clue,
        }));
        const st = PI.makeState(N, p.clues, seed);
        const res = PI.findAllDeductions(st, tech);
        if (!res || !res.steps.length) return null;

        const placedClue = new Set(state.placements.map((rc) => rc.clue));
        // A commit (Rule B) pins a clue to one whole rectangle. Each clue has
        // at most one, so there's nothing to merge — surface the first.
        const commit = res.steps.find((s) => s.kind === 'commit');
        if (commit) {
            const partial = placedClue.has(commit.clue);
            return {
                kind: 'deduce',
                rc: Object.assign({}, commit.rect, { clue: commit.clue }),
                clue: commit.clue,
                msgKey: partial ? 'patchesHint1' : 'patchesHint2',
            };
        }

        // forceCell (Rule A single-cover, or core): a clue can have SEVERAL
        // forced cells at once, in different directions. Group them by clue and
        // MERGE into one hint — its rectangle is the clue's current shape (its
        // placement, else clue cell) unioned with ALL its forced cells, and we
        // outline every one. Ship the richest group (most cells, then largest
        // area). Merging also subsumes the old "drop the contained smaller box"
        // de-domination, since a clue's cells collapse to their joint bounds.
        const byClue = new Map();
        for (const s of res.steps) {
            if (s.kind !== 'forceCell') continue;
            let g = byClue.get(s.clue);
            if (!g) byClue.set(s.clue, (g = { clue: s.clue, technique: s.technique, cells: [] }));
            g.cells.push(s.cell);
        }
        if (!byClue.size) return null;
        const groups = [...byClue.values()].map((g) => {
            const base = state.placements.find((rc) => rc.clue === g.clue) || null;
            const cl = p.clues[g.clue];
            const br0 = base ? base.r : cl.r, bc0 = base ? base.c : cl.c;
            const br1 = base ? base.r + base.h - 1 : cl.r, bc1 = base ? base.c + base.w - 1 : cl.c;
            // Box of the clue's current shape unioned with cell (r,c).
            const boxOf = (r, c) => ({
                r: Math.min(br0, r), c: Math.min(bc0, c),
                R: Math.max(br1, r), C: Math.max(bc1, c),
            });
            const area = (b) => (b.R - b.r + 1) * (b.C - b.c + 1);
            const holds = (o, m) => o.r <= m.r && o.c <= m.c && o.R >= m.R && o.C >= m.C;
            // Keep only cells that CONTRIBUTE a distinct implied rectangle.
            // Drop a cell whose box is contained in another cell's BIGGER box
            // (collinear "on the way" cells), and drop DUPLICATES when several
            // cells imply the SAME box (keep just the earliest — the player
            // drags a rectangle, so one supporting cell is enough to draw it).
            // What survives is the minimal set of corners the merged rectangle
            // needs; genuinely different-direction cells all remain.
            const boxes = g.cells.map(([r, c]) => boxOf(r, c));
            const cells = g.cells.filter((m, i) => !g.cells.some((o, j) => {
                if (j === i || !holds(boxes[j], boxes[i])) return false;
                const ao = area(boxes[j]), am = area(boxes[i]);
                return ao > am || (ao === am && j < i);
            }));
            let minR = br0, minC = bc0, maxR = br1, maxC = bc1;
            for (const [r, c] of cells) {
                minR = Math.min(minR, r); minC = Math.min(minC, c);
                maxR = Math.max(maxR, r); maxC = Math.max(maxC, c);
            }
            return { g, cells, rc: { r: minR, c: minC, w: maxC - minC + 1, h: maxR - minR + 1, clue: g.clue } };
        });
        groups.sort((a, b) => b.cells.length - a.cells.length
            || (b.rc.w * b.rc.h) - (a.rc.w * a.rc.h));
        const chosen = groups[0];
        const multi = chosen.cells.length > 1;
        const msgKey = chosen.g.technique === 'core'
            ? (multi ? 'patchesHintCoreMulti' : 'patchesHintCore')
            : (multi ? 'patchesHint3Multi' : 'patchesHint3');
        return {
            kind: 'deduce-cell',
            rc: chosen.rc,
            cells: chosen.cells,
            clue: chosen.g.clue,
            msgKey,
        };
    }

    function repaintHint() {
        const layer = board.querySelector('#hint');
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const h = state.hint;
        if (!h) return;
        const p = state.puzzle;
        const N = p.size;
        const cs = cellSize();

        // Cells that stay lit: the target rectangle(s) / cell and its clue cell.
        const focus = new Set();
        const rcs = h.rcs || (h.rc ? [h.rc] : []);
        for (const rc of rcs) {
            for (let r = rc.r; r < rc.r + rc.h; r++) {
                for (let c = rc.c; c < rc.c + rc.w; c++) focus.add(r * N + c);
            }
        }
        if (h.cells) for (const [r, c] of h.cells) focus.add(r * N + c);
        if (h.clue != null) { const cl = p.clues[h.clue]; focus.add(cl.r * N + cl.c); }

        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (focus.has(r * N + c)) continue;
                layer.appendChild(PC.svgEl('rect', {
                    class: 'patch-hint-dim',
                    x: c * cs, y: r * cs, width: cs, height: cs,
                }));
            }
        }

        const inset = Math.max(2, cs * 0.06);
        const rad = Math.max(3, cs * 0.1);
        const outline = (r, c, w, h2, dngr) => layer.appendChild(PC.svgEl('rect', {
            class: 'patch-hint-outline' + (dngr ? ' danger' : ''),
            x: c * cs + inset, y: r * cs + inset,
            width: w * cs - inset * 2, height: h2 * cs - inset * 2,
            rx: rad, ry: rad,
        }));
        // The outline marks the "protagonist"; the lit (undimmed) area is the
        // rectangle the hint suggests the player draw (h.rc).
        //   deduce (tier 1/2)   → outline the clue (shape) cell.
        //   deduce-cell         → outline every forced cell (may be several).
        //   wrong               → red-outline EVERY offending rectangle.
        //   conflict            → red-outline the offending rectangle.
        if (h.kind === 'deduce-cell' && h.cells) {
            for (const [r, c] of h.cells) outline(r, c, 1, 1, false);
        } else if (h.kind === 'deduce' && h.clue != null) {
            const cl = p.clues[h.clue];
            outline(cl.r, cl.c, 1, 1, false);
        } else if (h.kind === 'wrong') {
            for (const rc of rcs) outline(rc.r, rc.c, rc.w, rc.h, true);
        } else if (h.rc) {
            outline(h.rc.r, h.rc.c, h.rc.w, h.rc.h, h.kind === 'conflict');
        }
    }

    // -----------------------------------------------------------------
    // Pointer / drag interaction
    // -----------------------------------------------------------------

    /** Map an event to a grid cell, or null if outside the board. The SVG
     *  viewBox is "-3 -3 486 486", so the playable area is the inner
     *  480/486 offset by 3/486 on each side (same maths as Zip). */
    function eventToCell(ev) {
        const N = state.puzzle.size;
        const rect = board.getBoundingClientRect();
        if (rect.width === 0 || rect.height === 0) return null;
        const vbx = (ev.clientX - rect.left) / rect.width * 486 - 3;
        const vby = (ev.clientY - rect.top) / rect.height * 486 - 3;
        if (vbx < 0 || vbx >= BOARD_SIZE) return null;
        if (vby < 0 || vby >= BOARD_SIZE) return null;
        const cs = BOARD_SIZE / N;
        return [Math.floor(vby / cs), Math.floor(vbx / cs)];
    }

    function interactive() {
        return state.puzzle && !state.won && !shell.revealed;
    }

    function onPointerDown(ev) {
        if (!interactive()) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        const cell = eventToCell(ev);
        if (!cell) return;
        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        const [r, c] = cell;
        // Starting inside a placed rectangle picks it up to expand (grow-only);
        // its box seeds the gesture so the preview continues from its edges.
        const edit = state.placements.find((rc) => rectContainsCell(rc, r, c)) || null;
        state.drag = {
            pointerId: ev.pointerId,
            sr: r, sc: c,
            moved: false,
            editClue: edit ? edit.clue : -1,
            minR: edit ? edit.r : r,
            maxR: edit ? edit.r + edit.h - 1 : r,
            minC: edit ? edit.c : c,
            maxC: edit ? edit.c + edit.w - 1 : c,
        };
        repaintPreview();
    }

    function onPointerMove(ev) {
        const d = state.drag;
        if (!d || ev.pointerId !== d.pointerId) return;
        const cell = eventToCell(ev);
        if (!cell) return;
        const [r, c] = cell;
        if (r !== d.sr || c !== d.sc) d.moved = true;

        // Candidate box = current box unioned with the pointer cell. Reject
        // the growth if it would enclose a second clue (never let a preview
        // straddle two clues, matching the LinkedIn rule). The box only
        // ever grows within a single gesture.
        const nMinR = Math.min(d.minR, r);
        const nMaxR = Math.max(d.maxR, r);
        const nMinC = Math.min(d.minC, c);
        const nMaxC = Math.max(d.maxC, c);
        if (nMinR === d.minR && nMaxR === d.maxR
            && nMinC === d.minC && nMaxC === d.maxC) return;
        if (cluesInBox(nMinR, nMinC, nMaxR, nMaxC).count >= 2) return;
        // Reject growth that would overlap an already-placed rectangle —
        // same guard style as the two-clue rule — so placements stay
        // non-overlapping. The rectangle currently being expanded is exempt
        // (its own box is where this gesture started).
        const cand = { r: nMinR, c: nMinC, w: nMaxC - nMinC + 1, h: nMaxR - nMinR + 1 };
        for (const rc of state.placements) {
            if (rc.clue === d.editClue) continue;
            if (rectsOverlap(rc, cand)) return;
        }
        d.minR = nMinR; d.maxR = nMaxR; d.minC = nMinC; d.maxC = nMaxC;
        repaintPreview();
    }

    function onPointerUp(ev) {
        const d = state.drag;
        if (!d || ev.pointerId !== d.pointerId) return;
        try { board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        state.drag = null;

        // Snapshot the pre-change board (one gesture = one undo step), but
        // only when the gesture will actually mutate something.
        let willChange;
        if (!d.moved) {
            willChange = placementIndexUnder(d.sr, d.sc) >= 0;
        } else {
            const w = d.maxC - d.minC + 1;
            const h = d.maxR - d.minR + 1;
            willChange = w * h >= 2
                && cluesInBox(d.minR, d.minC, d.maxR, d.maxC).count === 1;
        }
        if (willChange) pushUndo();

        if (!d.moved) {
            if (placementIndexUnder(d.sr, d.sc) >= 0) {
                // Click on a placed rectangle removes it.
                deleteAt(d.sr, d.sc);
            } else if (cluesInBox(d.sr, d.sc, d.sr, d.sc).count === 1) {
                // Tapped a lone clue cell: a single cell can't be a region —
                // every patch is at least 2 cells — so nothing is placed.
                // Nudge the player to drag instead of silently doing nothing.
                if (PC.toast) PC.toast.show(PC.i18n.t('patchesMinSize'));
            }
        } else {
            placeFromBox(d);
        }
        repaintPreview();
        commitChange();
    }

    function onPointerCancel(ev) {
        if (!state.drag || ev.pointerId !== state.drag.pointerId) return;
        state.drag = null;
        repaintPreview();
    }

    function placeFromBox(d) {
        const w = d.maxC - d.minC + 1;
        const h = d.maxR - d.minR + 1;
        if (w * h < 2) return;                 // 1×1 is never a placement
        const { count, idx } = cluesInBox(d.minR, d.minC, d.maxR, d.maxC);
        if (count !== 1) return;               // must cover exactly one clue
        // Overlaps are already prevented during the drag, so the only thing
        // to clear here is a prior rectangle for the same clue (one per clue).
        state.placements = state.placements.filter((rc) => rc.clue !== idx);
        state.placements.push({ r: d.minR, c: d.minC, w, h, clue: idx });
    }

    function deleteAt(r, c) {
        for (let i = state.placements.length - 1; i >= 0; i--) {
            if (rectContainsCell(state.placements[i], r, c)) {
                state.placements.splice(i, 1);
                return;
            }
        }
    }

    // -----------------------------------------------------------------
    // Shell callbacks
    // -----------------------------------------------------------------

    async function startNewGame() {
        const seed = pendingSeed != null
            ? pendingSeed
            : ((Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0);
        pendingSeed = null;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        rebuildIndices();
        resetPlacements();
        if (undoHistory) undoHistory.clear();
        renderBoard();
        clearViolationDisplay();
        clearHint();
        updateStatusRow();
        updateUndoButton();
        if (PC.share) {
            PC.share.replaceUrl({
                size: shell.size, difficulty: shell.difficulty, seed,
            });
        }
        if (DEMO) applyDemo();
    }

    async function onShareClick() {
        if (!PC.share) return;
        const ok = await PC.share.copyCurrentUrl();
        if (PC.toast) PC.toast.show(PC.i18n.t(ok ? 'shareCopied' : 'shareFailed'));
    }

    function onKeyDown(ev) {
        if (!state.puzzle) return;
        if ((ev.ctrlKey || ev.metaKey) && !ev.shiftKey && !ev.altKey
            && (ev.key === 'z' || ev.key === 'Z')) {
            doUndo();
            ev.preventDefault();
        }
    }

    // Which hint each ?patches_demo=<technique> targets (matched by msgKey).
    // Like ?sudoku_demo: regenerate until the puzzle actually needs it, follow
    // the forced placements up to it, then pop that hint. Use diff=hard for
    // core/orphan. [DEBUG-HOOK]
    const DEMO_TECH = {
        commit: ['patchesHint1', 'patchesHint2'],
        tier3: ['patchesHint3'],
        core: ['patchesHintCore'],
    };
    let demoTries = 0;

    // Demo affordances (see ?patches_demo). 'hint' just opens a hint on the
    // fresh board; 'conflict' plants a guaranteed size-over violation.
    function applyDemo() {
        if (DEMO === 'hint') { onHint(); return; }
        if (DEMO === 'hint3') { demoTier3(); return; }
        if (DEMO === 'win') {
            state.placements = state.puzzle.solution.map((s) => ({
                r: s.r, c: s.c, w: s.w, h: s.h, clue: s.clue,
            }));
            commitChange(); // triggers the win state + animation
            return;
        }
        if (DEMO_TECH[DEMO]) { demoWalkToTechnique(DEMO_TECH[DEMO]); return; }
        if (DEMO !== 'conflict') return;
        const p = state.puzzle;
        const N = p.size;
        const numbered = p.solution.filter((s) => p.clues[s.clue].size != null);
        for (const base of numbered) {
            const grown = growByOne(base, N, base.clue, p.clues);
            if (grown) {
                grown.clue = base.clue;
                state.placements = [grown];
                repaintRects();
                showViolations();
                return;
            }
        }
    }

    // Follow "place this rectangle" hints until a forced-cell hint surfaces
    // (tier-3 / core / orphan — all `deduce-cell`), then show it.
    function demoTier3() {
        for (let step = 0; step < state.puzzle.clues.length; step++) {
            const h = computeHint();
            if (h.kind === 'deduce-cell') {
                state.hint = h; repaintHint(); setHintBanner(hintText(h)); return;
            }
            if (h.kind !== 'deduce') return;
            state.placements.push({ r: h.rc.r, c: h.rc.c, w: h.rc.w, h: h.rc.h, clue: h.rc.clue });
            repaintRects();
        }
    }

    // Walk the current puzzle's forced placements until a hint whose msgKey is
    // in `keys` appears, then show it. If this puzzle never needs it, spin up a
    // fresh board and try again (bounded) — same spirit as ?sudoku_demo.
    function demoWalkToTechnique(keys) {
        for (let step = 0; step < state.puzzle.clues.length + 5; step++) {
            const h = computeHint();
            if (!h) break;
            if (keys.includes(h.msgKey)) {
                state.hint = h; repaintHint(); setHintBanner(hintText(h)); return;
            }
            if (h.kind !== 'deduce' && h.kind !== 'deduce-cell') break; // none/conflict/wrong
            // Advance by locking in that clue's full solution rectangle.
            const sol = state.puzzle.solution.find((s) => s.clue === h.clue);
            if (!sol) break;
            state.placements = state.placements.filter((rc) => rc.clue !== sol.clue);
            state.placements.push({ r: sol.r, c: sol.c, w: sol.w, h: sol.h, clue: sol.clue });
            repaintRects();
        }
        if (demoTries++ < 80) {
            startNewGame();
        } else {
            /* eslint-disable no-console */
            console.warn(`[patches demo] "${DEMO}" not reached — try diff=hard for core/orphan.`);
            /* eslint-enable no-console */
        }
    }

    function growByOne(base, N, ownIdx, clues) {
        const opts = [
            { r: base.r, c: base.c, w: base.w + 1, h: base.h },       // right
            { r: base.r, c: base.c - 1, w: base.w + 1, h: base.h },   // left
            { r: base.r, c: base.c, w: base.w, h: base.h + 1 },       // down
            { r: base.r - 1, c: base.c, w: base.w, h: base.h + 1 },   // up
        ];
        for (const o of opts) {
            if (o.r < 0 || o.c < 0 || o.r + o.h > N || o.c + o.w > N) continue;
            if (boxHasForeignClue(o.r, o.c, o.r + o.h - 1, o.c + o.w - 1, ownIdx, clues)) {
                continue;
            }
            return o;
        }
        return null;
    }

    function resetAction() {
        if (!state.puzzle) return;
        // Mid-game Reset is undoable; a post-win Reset ends the session and
        // discards its undo history.
        if (state.won) { if (undoHistory) undoHistory.clear(); }
        else pushUndo();
        resetPlacements();
        clearViolationDisplay();
        clearHint();
        repaintRects();
        repaintClues();
        updateStatusRow();
        updateUndoButton();
    }

    function onReveal(revealed) {
        // Cancel any in-flight drag when flipping into reveal mode.
        state.drag = null;
        clearHint();
        repaintPreview();
        repaintRects();
        if (revealed) clearViolationDisplay();
        else scheduleViolations();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'patches',
            difficulty: { default: (urlInitial && urlInitial.difficulty) || 'medium' },
            size: {
                kind: 'slider', min: MIN_SIZE, max: MAX_SIZE,
                default: (urlInitial && urlInitial.size) || 8,
            },
            onNewGame: startNewGame,
            onReset: resetAction,
            onReveal,
        });
        board = shell.dom.board;
        hintBanner = document.getElementById('hint-banner');
        if (shell.dom.hintBtn) shell.dom.hintBtn.addEventListener('click', onHint);
        PC.i18n.subscribe(onLocaleChange);
        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerUp);
        board.addEventListener('pointercancel', onPointerCancel);
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());
        window.addEventListener('keydown', onKeyDown);

        undoHistory = PC.history.create({
            limit: 20,
            snapshot: snapshotState,
            restore: restoreSnapshot,
        });

        const shareBtn = document.getElementById('share-btn');
        if (shareBtn) shareBtn.addEventListener('click', onShareClick);
        const undoBtn = document.getElementById('undo-btn');
        if (undoBtn) undoBtn.addEventListener('click', doUndo);

        if (DEBUG) {
            window.__patches = { state, isWin, commitChange, repaintRects };
        }
        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
