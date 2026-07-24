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

    const BOARD_SIZE = 480;
    const MIN_SIZE = 5;
    const MAX_SIZE = 12;

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
        // Active pointer gesture. A gesture that never leaves its start
        // cell is a "click" (delete); one that moves is a "drag" (draw).
        drag: null,       // { pointerId, sr, sc, minR, maxR, minC, maxC, moved }
    };

    let shell = null;
    let board = null;
    let clueAt = null;    // Map "r,c" -> clue index, rebuilt per puzzle

    function resetPlacements() {
        state.placements = [];
        state.won = false;
        state.drag = null;
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
        layer.appendChild(PC.svgEl('rect', {
            class: 'patch-preview' + (tinted ? ' tinted' : ''),
            x: d.minC * cs + inset,
            y: d.minR * cs + inset,
            width: (d.maxC - d.minC + 1) * cs - inset * 2,
            height: (d.maxR - d.minR + 1) * cs - inset * 2,
            rx: radius, ry: radius,
            fill: color, stroke: color,
        }));
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
        const inset = Math.max(2, cs * 0.06);
        const radius = Math.max(3, cs * 0.10);

        for (const rc of rects) {
            const color = clueColor(rc.clue);
            layer.appendChild(PC.svgEl('rect', {
                class: 'patch-rect' + (showSolution ? ' reveal' : ''),
                x: rc.c * cs + inset,
                y: rc.r * cs + inset,
                width: rc.w * cs - inset * 2,
                height: rc.h * cs - inset * 2,
                rx: radius, ry: radius,
                fill: color,
                stroke: color,
            }));
        }
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
        const unit = cs * 0.6;          // long side of the swatch
        const shortSide = unit * 0.62;  // short side for wide/tall
        const rx = Math.max(2, cs * 0.06);

        function swatch(w, h, extra) {
            return PC.svgEl('rect', Object.assign({
                class: 'clue-swatch',
                x: cx - w / 2, y: cy - h / 2, width: w, height: h,
                rx, ry: rx, fill: color,
            }, extra || {}));
        }

        if (clue.shape === SQUARE) {
            g.appendChild(swatch(unit, unit));
        } else if (clue.shape === WIDE) {
            g.appendChild(swatch(unit, shortSide));
        } else if (clue.shape === TALL) {
            g.appendChild(swatch(shortSide, unit));
        } else {
            // any → overlapping dashed wide + tall, translucent.
            const dash = `${Math.max(2, cs * 0.05)} ${Math.max(2, cs * 0.04)}`;
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
                dy: '0.02em',
                'font-size': Math.max(11, cs * 0.32),
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
        repaintRects();
        if (!state.won && isWin()) {
            state.won = true;
            shell.markSolved();
            repaintRects();
        }
        updateStatusRow();
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
        state.drag = {
            pointerId: ev.pointerId,
            sr: r, sc: c,
            minR: r, maxR: r, minC: c, maxC: c,
            moved: false,
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
        // same guard style as the two-clue rule. Placements therefore stay
        // non-overlapping; to change a rectangle, delete it first (click)
        // then redraw.
        const cand = { r: nMinR, c: nMinC, w: nMaxC - nMinC + 1, h: nMaxR - nMinR + 1 };
        for (const rc of state.placements) {
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
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        rebuildIndices();
        resetPlacements();
        renderBoard();
        updateStatusRow();
    }

    function resetAction() {
        if (!state.puzzle) return;
        resetPlacements();
        repaintRects();
        repaintClues();
        updateStatusRow();
    }

    function onReveal() {
        // Cancel any in-flight drag when flipping into reveal mode.
        state.drag = null;
        repaintPreview();
        repaintRects();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'patches',
            difficulty: { default: 'medium' },
            size: { kind: 'slider', min: MIN_SIZE, max: MAX_SIZE, default: 8 },
            onNewGame: startNewGame,
            onReset: resetAction,
            onReveal,
        });
        board = shell.dom.board;
        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerUp);
        board.addEventListener('pointercancel', onPointerCancel);
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());
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
