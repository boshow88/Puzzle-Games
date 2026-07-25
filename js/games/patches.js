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
        const m = /[?&]patches_demo=([a-z]+)/.exec(location.search);
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

    function readUrlInitial() {
        if (!PC.share) return null;
        const raw = PC.share.readParams();
        if (!VALID_SIZES.has(raw.size)) return null;
        if (!VALID_DIFFS.has(raw.difficulty)) return null;
        if (!Number.isInteger(raw.seed)) return null;
        return { size: raw.size, difficulty: raw.difficulty, seed: raw.seed };
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
        // 2) A rule-valid rectangle that doesn't match the unique solution.
        const wrong = findWrongPlacement();
        if (wrong) {
            return { kind: 'wrong', rc: wrong, clue: wrong.clue, msgKey: 'patchesHintWrong' };
        }
        // 3) The next logical deduction.
        return computeDeduction() || { kind: 'none', msgKey: 'patchesHintNone' };
    }

    function findWrongPlacement() {
        const sol = new Map();
        for (const s of state.puzzle.solution) sol.set(s.clue, s);
        for (const rc of state.placements) {
            const s = sol.get(rc.clue);
            // Wrong only if it strays OUTSIDE its clue's solution rectangle.
            // A rectangle fully inside is a valid partial that can still be
            // expanded to the solution — a hint guides its completion instead.
            if (!s || rc.r < s.r || rc.c < s.c
                || rc.r + rc.h > s.r + s.h || rc.c + rc.w > s.c + s.w) return rc;
        }
        return null;
    }

    function computeDeduction() {
        const p = state.puzzle;
        const N = p.size;
        const PI = window.PuzzleGenerators.patchesInternals;
        const clueAtArr = PI.makeClueAt(N, p.clues);

        // The player's committed cells are LOWER BOUNDS only — a placed patch
        // may still grow. We deliberately don't consult the solution here, so
        // every deduction is sound pure logic (no "this patch is done because
        // the answer says so", which was making tier-3 reasoning wrong).
        const owner = new Int32Array(N * N).fill(-1);
        const placementByClue = new Map();
        for (const rc of state.placements) {
            placementByClue.set(rc.clue, rc);
            for (let r = rc.r; r < rc.r + rc.h; r++) {
                for (let c = rc.c; c < rc.c + rc.w; c++) owner[r * N + c] = rc.clue;
            }
        }
        // Usable by clue i iff it covers no cell owned by ANOTHER clue.
        const freeFor = (R, i) => {
            for (let r = R.r; r < R.r + R.h; r++) {
                for (let c = R.c; c < R.c + R.w; c++) {
                    const o = owner[r * N + c];
                    if (o !== -1 && o !== i) return false;
                }
            }
            return true;
        };
        const contains = (R, inner) => R.r <= inner.r && R.c <= inner.c
            && R.r + R.h >= inner.r + inner.h && R.c + R.w >= inner.c + inner.w;

        // Every clue's still-valid rectangles: those ⊇ its placement (if any)
        // that cover no cell owned by another clue. A placed patch's possible
        // EXPANSIONS are included, so it counts as able to reach nearby free
        // cells — that's what fixes the bad tier-3 (a no-size neighbour that
        // could grow to cover a cell is no longer ignored).
        const sameRect = (a, b) => a.r === b.r && a.c === b.c && a.w === b.w && a.h === b.h;
        const active = [];
        for (let i = 0; i < p.clues.length; i++) {
            const partial = placementByClue.get(i) || null;
            let cands = PI.enumerateCandidates(N, p.clues[i], i, clueAtArr)
                .filter((R) => freeFor(R, i));
            if (partial) cands = cands.filter((R) => contains(R, partial));
            active.push({ i, partial, cands });
        }

        // Gather every candidate deduction across all rules.
        const candidates = [];
        // Tier 1 (partial clue, single completion) & Tier 2 (unplaced clue,
        // single placement) — both suggest that clue's full rectangle.
        for (const a of active) {
            if (a.cands.length !== 1) continue;
            const only = a.cands[0];
            // A placed patch whose one rectangle is exactly what's already
            // there is complete — nothing to suggest.
            if (a.partial && sameRect(only, a.partial)) continue;
            candidates.push({
                kind: 'deduce', rc: Object.assign({}, only, { clue: a.i }),
                clue: a.i, tier: a.partial ? 1 : 2,
                msgKey: a.partial ? 'patchesHint1' : 'patchesHint2',
            });
        }
        // Tier 3 — non-clue empty cells only one clue's region can reach; the
        // suggested rectangle is the minimal drag from the clue to that cell.
        const coverClue = new Int32Array(N * N).fill(-1);
        const coverCount = new Int32Array(N * N);
        for (const a of active) {
            const seen = new Set();
            for (const R of a.cands) {
                for (let r = R.r; r < R.r + R.h; r++) {
                    for (let c = R.c; c < R.c + R.w; c++) {
                        const k = r * N + c;
                        if (seen.has(k)) continue;
                        seen.add(k);
                        if (coverClue[k] !== a.i) { coverCount[k] += 1; coverClue[k] = a.i; }
                    }
                }
            }
        }
        for (let k = 0; k < N * N; k++) {
            if (owner[k] !== -1 || coverCount[k] !== 1) continue;
            const r = (k / N) | 0;
            const c = k % N;
            if (clueIndexAt(r, c) >= 0) continue; // clue cells belong to self, trivially
            const clue = coverClue[k];
            const cl = p.clues[clue];
            // Grow FROM the player's current shape: use its partial rectangle's
            // bounds if one is placed (so the highlight includes what they've
            // already drawn), else just the clue cell. The suggested rectangle
            // is that base unioned with the target cell.
            const base = placementByClue.get(clue);
            const r0 = base ? base.r : cl.r;
            const c0 = base ? base.c : cl.c;
            const r1 = base ? base.r + base.h - 1 : cl.r;
            const c1 = base ? base.c + base.w - 1 : cl.c;
            const minR = Math.min(r0, r);
            const minC = Math.min(c0, c);
            const maxR = Math.max(r1, r);
            const maxC = Math.max(c1, c);
            const rc = {
                r: minR, c: minC, w: maxC - minC + 1, h: maxR - minR + 1, clue,
            };
            candidates.push({ kind: 'deduce-cell', rc, cell: [r, c], clue, tier: 3, msgKey: 'patchesHint3' });
        }

        // Drop any hint dominated by a STRONGER hint on the SAME clue — one
        // whose suggested rectangle strictly contains this one's (e.g. a small
        // tier-3 drag box sitting inside that clue's full placement, or a
        // shorter reach when a longer forced reach exists).
        const area = (t) => t.w * t.h;
        const encloses = (o, t) => o.r <= t.r && o.c <= t.c
            && o.r + o.h >= t.r + t.h && o.c + o.w >= t.c + t.w;
        const kept = candidates.filter((h) => !candidates.some((o) =>
            o !== h && o.clue === h.clue && area(o.rc) > area(h.rc) && encloses(o.rc, h.rc)));

        // Then honour the tier priority (1 → 2 → 3); Array.sort is stable, so
        // ties keep their scan order (clue index, then row-major cells).
        kept.sort((a, b) => a.tier - b.tier);
        return kept[0] || null;
    }

    function repaintHint() {
        const layer = board.querySelector('#hint');
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const h = state.hint;
        if (!h) return;
        const p = state.puzzle;
        const N = p.size;
        const cs = cellSize();

        // Cells that stay lit: the target rectangle / cell and its clue cell.
        const focus = new Set();
        if (h.rc) {
            for (let r = h.rc.r; r < h.rc.r + h.rc.h; r++) {
                for (let c = h.rc.c; c < h.rc.c + h.rc.w; c++) focus.add(r * N + c);
            }
        }
        if (h.cell) focus.add(h.cell[0] * N + h.cell[1]);
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

        const danger = h.kind === 'conflict' || h.kind === 'wrong';
        const cls = 'patch-hint-outline' + (danger ? ' danger' : '');
        const inset = Math.max(2, cs * 0.06);
        const rad = Math.max(3, cs * 0.1);
        const outline = (r, c, w, h2) => layer.appendChild(PC.svgEl('rect', {
            class: cls,
            x: c * cs + inset, y: r * cs + inset,
            width: w * cs - inset * 2, height: h2 * cs - inset * 2,
            rx: rad, ry: rad,
        }));
        // The outline marks the "protagonist"; the lit (undimmed) area is the
        // rectangle the hint wants the player to draw (h.rc).
        //   tier 3         → outline the forced cell.
        //   tier 1/2       → outline the clue (shape) cell, so "this outlined
        //                    shape" points clearly at the clue itself.
        //   conflict/wrong → outline the offending placed rectangle.
        if (h.kind === 'deduce-cell' && h.cell) {
            outline(h.cell[0], h.cell[1], 1, 1);
        } else if (h.kind === 'deduce' && h.clue != null) {
            const cl = p.clues[h.clue];
            outline(cl.r, cl.c, 1, 1);
        } else if (h.rc) {
            outline(h.rc.r, h.rc.c, h.rc.w, h.rc.h);
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
            // Click: delete the placed rectangle under the start cell.
            deleteAt(d.sr, d.sc);
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

    // Follow tier-1/2 hints (placing each forced rectangle) until a tier-3
    // cell hint surfaces, then show it — for eyeballing the tier-3 visual.
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
            difficulty: { default: urlInitial ? urlInitial.difficulty : 'medium' },
            size: {
                kind: 'slider', min: MIN_SIZE, max: MAX_SIZE,
                default: urlInitial ? urlInitial.size : 8,
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
