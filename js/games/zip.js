/**
 * Zip — gameplay, dummy puzzle generation, and SVG rendering.
 *
 * Same architectural shape as the other three games (deliberately), but
 * with a drag-based path-drawing interaction model instead of the
 * single-cell toggle / select / fill loops. Only depends on
 * window.PuzzleCommon.
 *
 * Puzzle JSON contract:
 *   {
 *     id:          string,
 *     game:        'zip',
 *     size:        N,                 // 5..12
 *     difficulty:  'easy' | 'medium' | 'hard',
 *     holes:       Array<[r, c]>,     // grey, unenterable cells
 *     walls:       Array<[[r,c],[r,c]]>,  // 4-adj cell pairs the path can't cross
 *     checkpoints: Array<{ r, c, n }>,   // 1..K numbered markers, n in path order
 *     solution:    Array<[r, c]>,     // canonical path covering all non-hole cells
 *   }
 *
 * The current generator is intentionally simple: random DFS through the
 * grid produces a path P; cells not in P become holes; checkpoints are
 * sampled along P at positions that match the difficulty; a few
 * incidental walls are dropped between non-P-adjacent cell pairs purely
 * for visual texture (they don't affect solvability of P). It does NOT
 * guarantee a unique solution — the proper generator will replace this
 * one later.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const BOARD_SIZE = 480;
    const MIN_SIZE = 5;
    const MAX_SIZE = 12;

    // -----------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------

    function cellKey(r, c) { return `${r},${c}`; }

    /** Canonical key for an unordered edge between two cells. */
    function edgeKey(a, b) {
        const [r1, c1] = a;
        const [r2, c2] = b;
        if (r1 < r2 || (r1 === r2 && c1 < c2)) {
            return `${r1},${c1}|${r2},${c2}`;
        }
        return `${r2},${c2}|${r1},${c1}`;
    }

    function isAdjacent4(a, b) {
        return Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) === 1;
    }

    // -----------------------------------------------------------------
    // Puzzle generation — delegates to the shared generator, driven through
    // the unified determinate progress bar (mirrors the other games).
    // -----------------------------------------------------------------

    async function generatePuzzle(size, difficulty, seed) {
        // Generation is one opaque compute (a single forceUnique search) with no
        // reliable sub-progress, so we DON'T drive a determinate bar — that would
        // just stall then jump. We leave the shell's progress overlay in its
        // indeterminate (sliding) mode by passing no onProgress; the slide is a
        // compositor animation, so it keeps moving even while the main thread is
        // blocked generating.
        return window.PuzzleGenerators.zip(size, difficulty, seed, null);
    }

    // Shareable-URL state: a link carries (size, diff, seed); the generator is
    // deterministic, so opening it reproduces the same board. The seed is used
    // once for the first board; New Game then rolls a fresh one and re-syncs
    // the address bar. Mirrors the other games.
    const VALID_DIFFS = new Set(['easy', 'medium', 'hard']);

    function readUrlInitial() {
        if (!PC.share) return null;
        const raw = PC.share.readParams();
        if (!(raw.size >= MIN_SIZE && raw.size <= MAX_SIZE)) return null;
        if (!VALID_DIFFS.has(raw.difficulty)) return null;
        if (!Number.isInteger(raw.seed)) return null;
        return { size: raw.size, difficulty: raw.difficulty, seed: raw.seed };
    }

    const urlInitial = readUrlInitial();
    let pendingSeed = urlInitial ? urlInitial.seed : null;

    async function onShareClick() {
        if (!PC.share) return;
        const ok = await PC.share.copyCurrentUrl();
        if (PC.toast) PC.toast.show(PC.i18n.t(ok ? 'shareCopied' : 'shareFailed'));
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        path: [],                   // Array<[r, c]>; player's current path
        dragging: null,             // { pointerId, lastCell: [r,c] } | null

        won: false,

        // Derived puzzle indices (rebuilt on every newPuzzle for fast lookups)
        holeSet: null,              // Set of "r,c"
        wallSet: null,              // Set of edgeKey
        checkpointMap: null,        // Map "r,c" -> number
        accessibleCount: 0,         // count of non-hole cells
    };

    let shell = null;
    let undoHistory = null;

    function rebuildPuzzleIndices() {
        const p = state.puzzle;
        state.holeSet = new Set(p.holes.map(([r, c]) => cellKey(r, c)));
        state.wallSet = new Set(p.walls.map(([a, b]) => edgeKey(a, b)));
        state.checkpointMap = new Map(p.checkpoints.map((cp) => [cellKey(cp.r, cp.c), cp.n]));
        state.accessibleCount = p.size * p.size - p.holes.length;
    }

    function resetPath() {
        state.path = [];
        state.dragging = null;
        state.won = false;
    }

    // -----------------------------------------------------------------
    // Undo (bounded snapshot history — one drag gesture = one step).
    // -----------------------------------------------------------------

    function clonePath(path) { return path.map((rc) => rc.slice()); }

    function snapshotState() { return { path: clonePath(state.path) }; }

    function restoreSnapshot(snap) {
        const wasWon = state.won;
        state.path = clonePath(snap.path);
        state.dragging = null;
        state.won = false;
        if (wasWon) shell.clearWin(); // reverse win chrome, resume the clock
        repaintCheckpoints();
        repaintPath();
        updateStatusRow();
    }

    function pushUndo() {
        if (!undoHistory || state.won) return;
        undoHistory.push();
        updateUndoButton();
    }

    // Undo stays available after winning (to review the last moves); it's only
    // cleared on Reset-after-win / New Game.
    function doUndo() {
        if (!state.puzzle) return;
        if (undoHistory && undoHistory.undo()) updateUndoButton();
    }

    function updateUndoButton() {
        const btn = document.getElementById('undo-btn');
        if (btn) btn.disabled = !(undoHistory && undoHistory.canUndo());
    }

    // -----------------------------------------------------------------
    // Rules
    // -----------------------------------------------------------------

    function isHole(r, c) {
        return state.holeSet.has(cellKey(r, c));
    }
    function hasWall(a, b) {
        return state.wallSet.has(edgeKey(a, b));
    }
    function checkpointAt(r, c) {
        const v = state.checkpointMap.get(cellKey(r, c));
        return v == null ? 0 : v;
    }
    function pathIndexOf(r, c) {
        for (let i = 0; i < state.path.length; i++) {
            if (state.path[i][0] === r && state.path[i][1] === c) return i;
        }
        return -1;
    }

    /**
     * Are the checkpoints visited in correct numerical order so far?
     * Returns the next-expected-checkpoint number if so, or null if the
     * path is already out of order.
     */
    function checkpointOrderState() {
        let expected = 1;
        for (const [r, c] of state.path) {
            const n = checkpointAt(r, c);
            if (n === 0) continue;
            if (n !== expected) return null;
            expected += 1;
        }
        return expected;
    }

    /**
     * Find the first index along the path where the checkpoint order
     * is broken (i.e. the player passed through, say, checkpoint 3
     * before reaching 2). Returns -1 if the order is currently valid.
     * Used both for the in-progress red tint and as a fast-path
     * invariant for the win check.
     */
    function computeWrongOrderStart() {
        let expected = 1;
        for (let i = 0; i < state.path.length; i++) {
            const [r, c] = state.path[i];
            const n = checkpointAt(r, c);
            if (n === 0) continue;
            if (n !== expected) return i;
            expected += 1;
        }
        return -1;
    }

    /**
     * The invalid (red) tail of the path, if any. Two ways to go wrong:
     *   • out-of-order: a checkpoint is reached before its predecessor — the
     *     offending cell and everything after it is red (tinted from it too);
     *   • overrun: the LAST checkpoint K is reached correctly but the path
     *     keeps going — the endpoint must be the final cell, so the segments
     *     leaving K (and the cells after it) are red, while K itself stays
     *     valid/blue.
     * Returns { lineFrom, tintFrom }: line segments with index > lineFrom are
     * red; cells with index >= tintFrom are tinted. Both -1 when the path is
     * currently valid.
     */
    function computeWrongRegion() {
        const w = computeWrongOrderStart();
        if (w >= 0) return { lineFrom: w, tintFrom: w };
        // Order is valid so far; check for an overrun past the final checkpoint.
        const K = state.puzzle.checkpoints.length;
        for (let i = 0; i < state.path.length - 1; i++) {
            const [r, c] = state.path[i];
            if (checkpointAt(r, c) === K) return { lineFrom: i, tintFrom: i + 1 };
        }
        return { lineFrom: -1, tintFrom: -1 };
    }

    function isWin() {
        if (state.path.length !== state.accessibleCount) return false;
        // All checkpoints visited in order? checkpointOrderState() will
        // be K+1 when all are hit correctly.
        const K = state.puzzle.checkpoints.length;
        const next = checkpointOrderState();
        if (next == null || next !== K + 1) return false;
        // The path must END at the highest-numbered checkpoint K, not
        // just pass through it on the way somewhere else.
        const [lastR, lastC] = state.path[state.path.length - 1];
        return checkpointAt(lastR, lastC) === K;
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    // Zip-specific DOM. The shell owns the toolbar / timer / win badge;
    // the path-progress pill is game-specific so we keep a ref here.
    let board = null;
    let pathProgressText = null;

    function cellCentre(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { cx: c * cs + cs / 2, cy: r * cs + cs / 2, cs };
    }

    function renderBoard() {
        const p = state.puzzle;
        const N = p.size;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        const cs = BOARD_SIZE / N;

        // Layer: cell backgrounds (white normally, grey for holes).
        // Fill is set inline because the shared `.cell-bg` CSS rule has
        // no default `fill` — see the comment in game.css.
        const bgGroup = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const hole = isHole(r, c);
                bgGroup.appendChild(PC.svgEl('rect', {
                    class: 'cell-bg' + (hole ? ' hole' : ''),
                    x: c * cs, y: r * cs, width: cs, height: cs,
                    fill: hole ? '#bdbdbd' : '#ffffff',
                }));
            }
        }
        svg.appendChild(bgGroup);

        // Layer: outer frame (same shared region-border style).
        const borderGroup = PC.svgEl('g', { class: 'region-borders' });
        const W = N * cs;
        const addBorder = (x1, y1, x2, y2) => {
            borderGroup.appendChild(PC.svgEl('line', {
                class: 'region-border', x1, y1, x2, y2,
            }));
        };
        addBorder(0, 0, W, 0);
        addBorder(0, W, W, W);
        addBorder(0, 0, 0, W);
        addBorder(W, 0, W, W);
        svg.appendChild(borderGroup);

        // Layer: persistent red tint on the cells that form a wrong-
        // -order portion of the path. Sits between the cells and the
        // path lines, so the line still draws on top (and itself gets
        // turned red over the same region).
        const wrongOrderGroup = PC.svgEl('g', { class: 'wrong-order' });
        wrongOrderGroup.setAttribute('id', 'wrong-order');
        svg.appendChild(wrongOrderGroup);

        // Layer: path (reveal underneath, then player path on top).
        const pathGroup = PC.svgEl('g', { class: 'paths' });
        pathGroup.setAttribute('id', 'paths');
        svg.appendChild(pathGroup);

        // Layer: short-lived red flashes for blocked drag attempts. Sits
        // above paths but below the path head and hit overlay so it
        // never covers the endpoint marker.
        const flashGroup = PC.svgEl('g', { class: 'flashes' });
        flashGroup.setAttribute('id', 'flashes');
        svg.appendChild(flashGroup);

        // Layer: walls (black thick lines on cell boundaries).
        const wallStroke = Math.max(5, Math.floor(cs * 0.10));
        const wallGroup = PC.svgEl('g', { class: 'walls' });
        for (const [a, b] of p.walls) {
            const [r1, c1] = a;
            const [r2, c2] = b;
            // Vertical wall between (r, c) and (r, c+1)
            let x1, y1, x2, y2;
            if (r1 === r2) {
                const x = Math.max(c1, c2) * cs;
                x1 = x; x2 = x;
                y1 = r1 * cs; y2 = (r1 + 1) * cs;
            } else {
                const y = Math.max(r1, r2) * cs;
                y1 = y; y2 = y;
                x1 = c1 * cs; x2 = (c1 + 1) * cs;
            }
            wallGroup.appendChild(PC.svgEl('line', {
                class: 'wall-line',
                x1, y1, x2, y2,
                'stroke-width': wallStroke,
            }));
        }
        svg.appendChild(wallGroup);

        // Layer: path head sits BELOW the checkpoints so a checkpoint
        // number is never obscured by the head. When the endpoint lands
        // on a checkpoint, the head circle is fully hidden by the cp;
        // we keep "endpoint here" visible by drawing an outer halo ring
        // (also in this group) whose stroke sticks out beyond the cp
        // outline.
        const headGroup = PC.svgEl('g', { class: 'path-head-group' });
        headGroup.setAttribute('id', 'path-head');
        svg.appendChild(headGroup);

        // Layer: checkpoint circles + numbers, above the head so the
        // number is always legible.
        const cpGroup = PC.svgEl('g', { class: 'checkpoints' });
        cpGroup.setAttribute('id', 'checkpoints');
        svg.appendChild(cpGroup);

        // Layer: invisible hit targets covering every cell — used to map
        // pointer events to a cell, including the holes (so we can
        // visually feed the pointer through them and reject the move).
        const hitGroup = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                hitGroup.appendChild(PC.svgEl('rect', {
                    class: 'cell-hover',
                    x: c * cs, y: r * cs, width: cs, height: cs,
                    'data-r': r,
                    'data-c': c,
                }));
            }
        }
        svg.appendChild(hitGroup);

        repaintCheckpoints();
        repaintPath();
    }

    function repaintCheckpoints() {
        const p = state.puzzle;
        const N = p.size;
        const group = board.querySelector('#checkpoints');
        while (group.firstChild) group.removeChild(group.firstChild);

        const { cs } = cellCentre(N, 0, 0);
        const radius = Math.max(10, Math.floor(cs * 0.32));
        const font = Math.max(12, Math.floor(cs * 0.42));
        const cls = state.won ? 'checkpoint-circle victory' : 'checkpoint-circle';

        for (const cp of p.checkpoints) {
            const cx = cp.c * cs + cs / 2;
            const cy = cp.r * cs + cs / 2;
            group.appendChild(PC.svgEl('circle', {
                class: cls,
                cx, cy, r: radius,
            }));
            const text = PC.svgEl('text', {
                class: 'checkpoint-text',
                x: cx, y: cy,
                'text-anchor': 'middle',
                'dominant-baseline': 'middle',
                // Digits sit visually lower than the dominant-baseline
                // mid; use the same dy as Sudoku digits, not the smaller
                // dy used for the top-heavy ♛ / ☀ / ☾ glyphs.
                dy: '0.12em',
                'font-size': font,
            });
            text.textContent = String(cp.n);
            group.appendChild(text);
        }
    }

    /** Interpolate the path colour at fractional position t in [0, 1].
     *  Correct segments: dark blue-grey (52, 73, 94) → bright blue
     *  (52, 152, 219). Wrong-order segments: dark red (132, 32, 41) →
     *  bright red (220, 53, 69) — `#dc3545`, the shared --accent-danger.
     *  Both gradients use the same t parameter computed over the WHOLE
     *  path, so a blue→red transition at the wrong-order boundary lines
     *  up at a similar depth. Victory turns everything gold. */
    function pathColorAt(t, won, wrong) {
        if (won) return 'rgb(212, 160, 23)';
        if (wrong) {
            const r = Math.round(132 + (220 - 132) * t);
            const g = Math.round(32 + (53 - 32) * t);
            const b = Math.round(41 + (69 - 41) * t);
            return `rgb(${r}, ${g}, ${b})`;
        }
        const g = Math.round(73 + (152 - 73) * t);
        const b = Math.round(94 + (219 - 94) * t);
        return `rgb(52, ${g}, ${b})`;
    }

    function repaintPath() {
        const p = state.puzzle;
        const N = p.size;
        const cs = BOARD_SIZE / N;

        // Invalid tail (out-of-order or overrun past the last checkpoint) —
        // compute once and reuse for both the cell tint and the per-segment
        // line colour. Skip entirely once the puzzle has been won.
        const region = state.won ? { lineFrom: -1, tintFrom: -1 } : computeWrongRegion();
        const wrongStart = region.lineFrom;
        const wrongLayer = board.querySelector('#wrong-order');
        while (wrongLayer.firstChild) wrongLayer.removeChild(wrongLayer.firstChild);
        if (region.tintFrom >= 0) {
            for (let i = region.tintFrom; i < state.path.length; i++) {
                const [r, c] = state.path[i];
                wrongLayer.appendChild(PC.svgEl('rect', {
                    class: 'wrong-order-tint',
                    x: c * cs, y: r * cs, width: cs, height: cs,
                }));
            }
        }

        const group = board.querySelector('#paths');
        while (group.firstChild) group.removeChild(group.firstChild);

        const stroke = Math.max(10, Math.floor(cs * 0.36));

        // Reveal solution path underneath the player's, drawn in green.
        if (shell.revealed && !state.won && p.solution.length >= 2) {
            const points = p.solution
                .map(([r, c]) => `${c * cs + cs / 2},${r * cs + cs / 2}`)
                .join(' ');
            group.appendChild(PC.svgEl('polyline', {
                class: 'zip-path reveal',
                points,
                'stroke-width': stroke * 0.6,
            }));
        }

        // Player path as a series of per-segment lines so each segment
        // can carry its own interpolated colour. Both the correct and
        // wrong-order gradients share the same t parameter over the
        // whole path, so the blue→red transition at the wrong-order
        // boundary lands at roughly the same depth. The segment that
        // *arrives at* the wrong checkpoint is still blue — only the
        // segments LEAVING the wrong cell switch to red, so the colour
        // change visually originates at the wrong number itself.
        if (state.path.length >= 2) {
            const segs = state.path.length - 1;
            for (let i = 1; i < state.path.length; i++) {
                const isWrong = wrongStart >= 0 && i > wrongStart;
                const t = segs > 0 ? i / segs : 0;
                const colour = pathColorAt(t, state.won, isWrong);
                const [r0, c0] = state.path[i - 1];
                const [r1, c1] = state.path[i];
                group.appendChild(PC.svgEl('line', {
                    class: 'zip-path',
                    x1: c0 * cs + cs / 2, y1: r0 * cs + cs / 2,
                    x2: c1 * cs + cs / 2, y2: r1 * cs + cs / 2,
                    style: `stroke: ${colour}`,
                    'stroke-width': stroke,
                }));
            }
        }

        // Path head: a larger circle that sits beneath the checkpoint
        // layer. When the endpoint coincides with a checkpoint, the
        // small circle is covered up by the cp, so we additionally draw
        // a halo ring whose stroke sticks out beyond the cp outline —
        // that's the "endpoint here" cue when the player has crossed
        // into a numbered cell. Both pieces switch to red whenever the
        // path is currently parked inside a wrong-order tail.
        const headGroup = board.querySelector('#path-head');
        while (headGroup.firstChild) headGroup.removeChild(headGroup.firstChild);
        if (state.path.length >= 1) {
            const [hr, hc] = state.path[state.path.length - 1];
            const cx = hc * cs + cs / 2;
            const cy = hr * cs + cs / 2;
            const headR = Math.max(8, Math.floor(cs * 0.27));
            // Reaching the final checkpoint before every cell is covered is a
            // dead end (you can't leave it without overrunning), so flag the
            // head red too — not just the out-of-order / overrun cases.
            const finalCp = state.puzzle.checkpoints.length;
            const headOnFinalEarly = !state.won && checkpointAt(hr, hc) === finalCp;
            const headState = state.won ? ' victory' : (wrongStart >= 0 || headOnFinalEarly ? ' wrong' : '');
            headGroup.appendChild(PC.svgEl('circle', {
                class: 'path-head' + headState, cx, cy, r: headR,
            }));
            if (checkpointAt(hr, hc) > 0) {
                // Place the ring so its INNER edge touches the cp's
                // outline. The ring's band then extends outward beyond
                // the cp, which reads as the head "spilling out" from
                // behind the cp rather than as a separate halo.
                const cpR = Math.max(10, Math.floor(cs * 0.32));
                const ringW = Math.max(5, Math.floor(cs * 0.09));
                const ringR = cpR + ringW / 2;
                headGroup.appendChild(PC.svgEl('circle', {
                    class: 'path-head-ring' + headState,
                    cx, cy, r: ringR,
                    fill: 'none',
                    'stroke-width': ringW,
                }));
            }
        }
    }

    /** Show a brief red wash on the given cell to indicate the drag
     *  hit an illegal target (wall, hole, etc.). Auto-removed after
     *  the CSS animation completes. */
    function flashInvalid(cell) {
        if (!state.puzzle) return;
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const layer = board.querySelector('#flashes');
        if (!layer) return;
        const rect = PC.svgEl('rect', {
            class: 'zip-invalid-flash',
            x: cell[1] * cs, y: cell[0] * cs,
            width: cs, height: cs,
        });
        layer.appendChild(rect);
        setTimeout(() => {
            if (rect.parentNode) rect.parentNode.removeChild(rect);
        }, 420);
    }

    function updateStatusRow() {
        const total = state.accessibleCount || 0;
        const have = state.path.length;
        pathProgressText.textContent = `${have} / ${total}`;
        shell.setWin(state.won);
    }

    // -----------------------------------------------------------------
    // Pointer / drag interaction
    // -----------------------------------------------------------------

    /** Map an event to a grid cell, or null if outside the board. */
    function eventToCell(ev) {
        const N = state.puzzle.size;
        const rect = board.getBoundingClientRect();
        if (rect.width === 0 || rect.height === 0) return null;
        // The SVG viewBox is "-3 -3 486 486", so the playable area sits
        // at viewBox coords (0..480, 0..480) which corresponds to the
        // inner (480/486) of the rendered SVG, offset by (3/486) on
        // each side.
        const vbx = (ev.clientX - rect.left) / rect.width * 486 - 3;
        const vby = (ev.clientY - rect.top) / rect.height * 486 - 3;
        if (vbx < 0 || vbx >= BOARD_SIZE) return null;
        if (vby < 0 || vby >= BOARD_SIZE) return null;
        const cs = BOARD_SIZE / N;
        return [Math.floor(vby / cs), Math.floor(vbx / cs)];
    }

    // Pure predicate mirroring tryStartDragAt's guards (no mutation), so the
    // pointerdown handler can snapshot for undo *before* the path is modified.
    function canStartDragAt(cell) {
        if (state.won) return false;
        const [r, c] = cell;
        if (isHole(r, c)) return false;
        if (state.path.length === 0) return checkpointAt(r, c) === 1;
        return pathIndexOf(r, c) >= 0;
    }

    function tryStartDragAt(cell, pointerId) {
        if (state.won) return false;
        const [r, c] = cell;
        if (isHole(r, c)) return false;
        if (state.path.length === 0) {
            // Path empty: only checkpoint "1" is a valid starting point.
            if (checkpointAt(r, c) !== 1) return false;
            state.path = [[r, c]];
        } else {
            // Path non-empty: cell must already be on the path. Click
            // truncates everything AFTER the clicked cell — so clicking
            // the current endpoint is a no-op, clicking the previous
            // cell rewinds by one, clicking far back resets to there.
            const idx = pathIndexOf(r, c);
            if (idx < 0) return false;
            state.path = state.path.slice(0, idx + 1);
        }
        state.dragging = { pointerId, lastCell: [r, c], lastFlashCell: null };
        return true;
    }

    /**
     * Try to update the path so that its endpoint moves to a single
     * 4-adjacent cell. Returns a status object the caller can use to
     * decide whether to repaint, flash, or stop walking:
     *   { kind: 'extend' }              moved forward into an empty cell
     *   { kind: 'retract' }             moved back onto the immediate
     *                                   predecessor (one-cell undo)
     *   { kind: 'noop' }                the cell is on the path but not
     *                                   the immediate predecessor; no
     *                                   change, no error
     *   { kind: 'nonadj' }              not 4-adjacent to the endpoint
     *   { kind: 'blocked', cell }       adjacent but blocked by a wall
     *                                   or a hole
     *   { kind: 'occupied', cell }      adjacent but already on the path —
     *                                   the head would run into its own body
     */
    function attemptStepTo(cell) {
        if (state.path.length === 0) return { kind: 'noop' };
        const [r, c] = cell;
        const endpoint = state.path[state.path.length - 1];
        if (endpoint[0] === r && endpoint[1] === c) return { kind: 'noop' };

        // Retract one cell when the cursor enters the cell immediately
        // before the endpoint. We deliberately don't retract when the
        // cursor lands on any other path cell — that avoids "accidental"
        // long-trims when a fast drag sweeps over the middle of the
        // existing path.
        if (state.path.length >= 2) {
            const prev = state.path[state.path.length - 2];
            if (prev[0] === r && prev[1] === c) {
                state.path.pop();
                return { kind: 'retract' };
            }
        }
        if (!isAdjacent4(endpoint, cell)) {
            // A far sweep over some middle cell of the path is not an attempt
            // to move there — stay silent; otherwise it's simply not reachable.
            return pathIndexOf(r, c) >= 0 ? { kind: 'noop' } : { kind: 'nonadj' };
        }
        // Adjacent to the head: flag the illegal targets so the caller flashes.
        if (pathIndexOf(r, c) >= 0) return { kind: 'occupied', cell };
        if (isHole(r, c)) return { kind: 'blocked', cell };
        if (hasWall(endpoint, cell)) return { kind: 'blocked', cell };
        state.path.push([r, c]);
        return { kind: 'extend' };
    }

    function onPointerDown(ev) {
        if (!state.puzzle) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        const cell = eventToCell(ev);
        if (!cell) return;
        if (!canStartDragAt(cell)) return;
        pushUndo();                             // snapshot the pre-gesture path
        tryStartDragAt(cell, ev.pointerId);     // guaranteed to start now
        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        repaintPath();
        updateStatusRow();
    }

    function onPointerMove(ev) {
        if (!state.dragging) return;
        if (ev.pointerId !== state.dragging.pointerId) return;
        const cell = eventToCell(ev);
        if (!cell) return;
        const last = state.dragging.lastCell;
        if (last && last[0] === cell[0] && last[1] === cell[1]) return;
        state.dragging.lastCell = cell;

        const result = attemptStepTo(cell);
        if (result.kind === 'blocked' || result.kind === 'occupied') {
            const lf = state.dragging.lastFlashCell;
            if (!lf || lf[0] !== result.cell[0] || lf[1] !== result.cell[1]) {
                flashInvalid(result.cell);
                state.dragging.lastFlashCell = result.cell;
            }
        } else {
            state.dragging.lastFlashCell = null;
        }
        if (result.kind !== 'extend' && result.kind !== 'retract') return;

        if (isWin() && !state.won) {
            state.won = true;
            shell.markSolved();
            // End the drag the instant the puzzle is solved. Without
            // this, the player can keep dragging through the same
            // gesture (e.g. accidentally pulling back over the
            // penultimate cell) and produce a partly-retracted "gold"
            // path that looks both won and unfinished.
            if (state.dragging) {
                try { board.releasePointerCapture(state.dragging.pointerId); } catch (_) { /* ignore */ }
                state.dragging = null;
            }
        }
        repaintPath();
        if (state.won) repaintCheckpoints();
        updateStatusRow();
    }

    function onPointerEnd(ev) {
        if (!state.dragging) return;
        if (ev.pointerId !== state.dragging.pointerId) return;
        try { board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        state.dragging = null;
    }

    // -----------------------------------------------------------------
    // Event handlers (toolbar / actions)
    // -----------------------------------------------------------------

    async function startNewGame() {
        const seed = (pendingSeed != null)
            ? pendingSeed
            : ((Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0);
        pendingSeed = null;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        rebuildPuzzleIndices();
        resetPath();
        if (undoHistory) undoHistory.clear();
        renderBoard();
        updateStatusRow();
        updateUndoButton();
        if (PC.share) {
            PC.share.replaceUrl({ size: shell.size, difficulty: shell.difficulty, seed });
        }
    }

    function resetPathAction() {
        if (!state.puzzle) return;
        // Mid-game Reset is undoable; a post-win Reset ends the session and
        // discards its undo history.
        if (state.won) { if (undoHistory) undoHistory.clear(); }
        else pushUndo();
        resetPath();
        repaintCheckpoints();
        repaintPath();
        updateStatusRow();
        updateUndoButton();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'zip',
            difficulty: { default: urlInitial ? urlInitial.difficulty : 'medium' },
            size: { kind: 'slider', min: MIN_SIZE, max: MAX_SIZE, default: urlInitial ? urlInitial.size : 7 },
            onNewGame: startNewGame,
            onReset: resetPathAction,
            onReveal: repaintPath,
        });
        board = shell.dom.board;
        pathProgressText = document.getElementById('path-progress-text');

        undoHistory = PC.history.create({
            limit: 20,
            snapshot: snapshotState,
            restore: restoreSnapshot,
        });

        const shareBtn = document.getElementById('share-btn');
        if (shareBtn) shareBtn.addEventListener('click', onShareClick);
        const undoBtn = document.getElementById('undo-btn');
        if (undoBtn) undoBtn.addEventListener('click', doUndo);
        // Ctrl/⌘+Z → undo (Shift not held, so we don't hijack redo chords).
        window.addEventListener('keydown', (ev) => {
            if ((ev.ctrlKey || ev.metaKey) && !ev.shiftKey && !ev.altKey && (ev.key === 'z' || ev.key === 'Z')) {
                doUndo();
                ev.preventDefault();
            }
        });

        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerEnd);
        board.addEventListener('pointercancel', onPointerEnd);
        // Don't let the browser kick in its own touch behaviours (scroll,
        // long-press) while the player is drawing — we already opt out of
        // panning via touch-action: manipulation on `.board-svg`, but
        // belt-and-braces this for older browsers.
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());

        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
