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

    /** Roughly how many checkpoints to place per board, by difficulty.
     *  Higher difficulty == fewer constraints, so more "free" planning. */
    const CHECKPOINT_DENSITY = {
        easy:   { min: 4, ratio: 0.20 },
        medium: { min: 3, ratio: 0.14 },
        hard:   { min: 2, ratio: 0.10 },
    };

    /** Fraction of "decorative" walls (between non-path-adjacent cells)
     *  to drop in. Capped so the board doesn't look too noisy. */
    const WALL_DENSITY = {
        easy:   0.04,
        medium: 0.08,
        hard:   0.14,
    };

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

    function neighbours4(N, r, c) {
        const out = [];
        if (r > 0) out.push([r - 1, c]);
        if (r < N - 1) out.push([r + 1, c]);
        if (c > 0) out.push([r, c - 1]);
        if (c < N - 1) out.push([r, c + 1]);
        return out;
    }

    function isAdjacent4(a, b) {
        return Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) === 1;
    }

    // -----------------------------------------------------------------
    // Dummy puzzle generator
    // -----------------------------------------------------------------

    /**
     * Generate a random Hamiltonian-ish path on an N×N grid by random
     * 4-connected DFS. The path may not cover every cell — uncovered
     * cells will become holes. Returns the path as an Array<[r, c]>.
     */
    function randomPath(N, rng) {
        const visited = new Set();
        const startR = PC.rng.pickInt(rng, 0, N);
        const startC = PC.rng.pickInt(rng, 0, N);
        const path = [[startR, startC]];
        visited.add(cellKey(startR, startC));

        // Iterative DFS-with-restart-on-stuck.
        while (true) {
            const [r, c] = path[path.length - 1];
            const candidates = neighbours4(N, r, c)
                .filter(([nr, nc]) => !visited.has(cellKey(nr, nc)));
            if (candidates.length === 0) break;
            PC.rng.shuffle(candidates, rng);
            const next = candidates[0];
            path.push(next);
            visited.add(cellKey(next[0], next[1]));
        }
        return path;
    }

    /**
     * Sample K checkpoint positions along the path. Positions 0 (start)
     * and last (end) are always checkpoints; the rest are spaced as
     * evenly as possible with a touch of jitter.
     */
    function pickCheckpointIndices(pathLen, K, rng) {
        if (K <= 1) return [0];
        if (K >= pathLen) return Array.from({ length: pathLen }, (_, i) => i);
        const out = new Set([0, pathLen - 1]);
        const step = (pathLen - 1) / (K - 1);
        for (let i = 1; i < K - 1; i++) {
            const ideal = Math.round(i * step);
            const jitter = PC.rng.pickInt(rng, -1, 2); // -1, 0, or 1
            const pos = PC.clamp(ideal + jitter, 1, pathLen - 2);
            out.add(pos);
        }
        return Array.from(out).sort((a, b) => a - b);
    }

    /**
     * Pick a set of "decorative" walls between cell pairs that are
     * adjacent in the grid but NOT consecutive in the path. These walls
     * never appear on P, so they don't block the canonical solution.
     */
    function pickDecorativeWalls(N, path, fraction, rng) {
        const pathEdges = new Set();
        for (let i = 1; i < path.length; i++) {
            pathEdges.add(edgeKey(path[i - 1], path[i]));
        }
        const candidates = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                for (const [nr, nc] of [[r, c + 1], [r + 1, c]]) {
                    if (nr >= N || nc >= N) continue;
                    const key = edgeKey([r, c], [nr, nc]);
                    if (pathEdges.has(key)) continue;
                    candidates.push([[r, c], [nr, nc]]);
                }
            }
        }
        PC.rng.shuffle(candidates, rng);
        const take = Math.min(candidates.length, Math.round(candidates.length * fraction));
        return candidates.slice(0, take);
    }

    function generatePuzzle(size, difficulty, seed) {
        const rng = PC.rng.make(seed);
        let path = null;
        // Retry generation a few times to avoid the rare very-short path.
        for (let attempt = 0; attempt < 6; attempt++) {
            const p = randomPath(size, rng);
            if (!path || p.length > path.length) path = p;
            if (path.length >= size * size * 0.5) break;
        }
        const cellsInPath = new Set(path.map(([r, c]) => cellKey(r, c)));
        const holes = [];
        for (let r = 0; r < size; r++) {
            for (let c = 0; c < size; c++) {
                if (!cellsInPath.has(cellKey(r, c))) holes.push([r, c]);
            }
        }

        const cd = CHECKPOINT_DENSITY[difficulty] || CHECKPOINT_DENSITY.medium;
        const K = Math.max(cd.min, Math.round(path.length * cd.ratio));
        const indices = pickCheckpointIndices(path.length, K, rng);
        const checkpoints = indices.map((idx, i) => ({
            r: path[idx][0],
            c: path[idx][1],
            n: i + 1,
        }));

        const wallDensity = WALL_DENSITY[difficulty] || WALL_DENSITY.medium;
        const walls = pickDecorativeWalls(size, path, wallDensity, rng);

        return {
            id: `zip-${size}x${size}-${difficulty}-${seed.toString(36)}`,
            game: 'zip',
            size,
            difficulty,
            holes,
            walls,
            checkpoints,
            solution: path,
        };
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        path: [],                   // Array<[r, c]>; player's current path
        dragging: null,             // { pointerId, lastCell: [r,c] } | null

        revealed: false,
        won: false,
        size: 7,
        difficulty: 'medium',

        // Derived puzzle indices (rebuilt on every newPuzzle for fast lookups)
        holeSet: null,              // Set of "r,c"
        wallSet: null,              // Set of edgeKey
        checkpointMap: null,        // Map "r,c" -> number
        accessibleCount: 0,         // count of non-hole cells

        timer: null,
    };

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

    const dom = {
        board: null,
        difficultySeg: null,
        sizeSlider: null,
        sizeReadout: null,
        newGameBtn: null,
        resetBtn: null,
        revealBtn: null,
        timer: null,
        pathProgress: null,
        pathProgressText: null,
        winMessage: null,
    };

    function cellCentre(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { cx: c * cs + cs / 2, cy: r * cs + cs / 2, cs };
    }

    function renderBoard() {
        const p = state.puzzle;
        const N = p.size;
        const svg = dom.board;
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
        const group = dom.board.querySelector('#checkpoints');
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
                dy: '0.08em',
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

        // Wrong-order region — compute once and reuse for both the cell
        // tint and the per-segment line colour. Skip entirely when the
        // puzzle has already been won (no longer in progress).
        const wrongStart = state.won ? -1 : computeWrongOrderStart();
        const wrongLayer = dom.board.querySelector('#wrong-order');
        while (wrongLayer.firstChild) wrongLayer.removeChild(wrongLayer.firstChild);
        if (wrongStart >= 0) {
            for (let i = wrongStart; i < state.path.length; i++) {
                const [r, c] = state.path[i];
                wrongLayer.appendChild(PC.svgEl('rect', {
                    class: 'wrong-order-tint',
                    x: c * cs, y: r * cs, width: cs, height: cs,
                }));
            }
        }

        const group = dom.board.querySelector('#paths');
        while (group.firstChild) group.removeChild(group.firstChild);

        const stroke = Math.max(10, Math.floor(cs * 0.36));

        // Reveal solution path underneath the player's, drawn in green.
        if (state.revealed && !state.won && p.solution.length >= 2) {
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
        const headGroup = dom.board.querySelector('#path-head');
        while (headGroup.firstChild) headGroup.removeChild(headGroup.firstChild);
        if (state.path.length >= 1) {
            const [hr, hc] = state.path[state.path.length - 1];
            const cx = hc * cs + cs / 2;
            const cy = hr * cs + cs / 2;
            const headR = Math.max(8, Math.floor(cs * 0.27));
            const headState = state.won ? ' victory' : (wrongStart >= 0 ? ' wrong' : '');
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
        const layer = dom.board.querySelector('#flashes');
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
        dom.pathProgressText.textContent = `${have} / ${total}`;
        dom.winMessage.hidden = !state.won;
    }

    // -----------------------------------------------------------------
    // Pointer / drag interaction
    // -----------------------------------------------------------------

    /** Map an event to a grid cell, or null if outside the board. */
    function eventToCell(ev) {
        const N = state.puzzle.size;
        const rect = dom.board.getBoundingClientRect();
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
        if (pathIndexOf(r, c) >= 0) return { kind: 'noop' };
        if (!isAdjacent4(endpoint, cell)) return { kind: 'nonadj' };
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
        if (!tryStartDragAt(cell, ev.pointerId)) return;
        ev.preventDefault();
        try { dom.board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
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
        if (result.kind === 'blocked') {
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
            const elapsed = state.timer ? state.timer.stop() : 0;
            PC.solves.log('zip', state.puzzle.size, state.puzzle.difficulty, elapsed);
            // End the drag the instant the puzzle is solved. Without
            // this, the player can keep dragging through the same
            // gesture (e.g. accidentally pulling back over the
            // penultimate cell) and produce a partly-retracted "gold"
            // path that looks both won and unfinished.
            if (state.dragging) {
                try { dom.board.releasePointerCapture(state.dragging.pointerId); } catch (_) { /* ignore */ }
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
        try { dom.board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        state.dragging = null;
    }

    // -----------------------------------------------------------------
    // Event handlers (toolbar / actions)
    // -----------------------------------------------------------------

    function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = generatePuzzle(state.size, state.difficulty, seed);
        rebuildPuzzleIndices();
        resetPath();
        state.revealed = false;
        dom.revealBtn.classList.remove('active');
        dom.revealBtn.setAttribute('aria-pressed', 'false');
        renderBoard();
        updateStatusRow();
        if (state.timer) state.timer.start();
    }

    function resetPath_action() {
        if (!state.puzzle) return;
        resetPath();
        repaintCheckpoints();
        repaintPath();
        updateStatusRow();
        if (state.timer) state.timer.start();
    }

    function toggleReveal() {
        state.revealed = !state.revealed;
        dom.revealBtn.classList.toggle('active', state.revealed);
        dom.revealBtn.setAttribute('aria-pressed', state.revealed ? 'true' : 'false');
        repaintPath();
    }

    function setDifficulty(value) {
        if (!['easy', 'medium', 'hard'].includes(value)) return;
        state.difficulty = value;
        dom.difficultySeg.querySelectorAll('button').forEach((btn) => {
            btn.classList.toggle('active', btn.dataset.value === value);
        });
        PC.prefs.set('zip', { difficulty: value });
        startNewGame();
    }

    function setSize(value) {
        const n = PC.clamp(parseInt(value, 10) || 7, MIN_SIZE, MAX_SIZE);
        state.size = n;
        dom.sizeSlider.value = String(n);
        dom.sizeReadout.textContent = `${n}×${n}`;
        PC.prefs.set('zip', { size: n });
        startNewGame();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        dom.board = document.getElementById('board');
        dom.difficultySeg = document.getElementById('difficulty-seg');
        dom.sizeSlider = document.getElementById('size-slider');
        dom.sizeReadout = document.getElementById('size-readout');
        dom.newGameBtn = document.getElementById('new-game-btn');
        dom.resetBtn = document.getElementById('reset-btn');
        dom.revealBtn = document.getElementById('reveal-btn');
        dom.timer = document.getElementById('timer');
        dom.pathProgress = document.getElementById('path-progress');
        dom.pathProgressText = document.getElementById('path-progress-text');
        dom.winMessage = document.getElementById('win-message');

        const prefs = PC.prefs.get('zip');
        if (prefs.difficulty) state.difficulty = prefs.difficulty;
        if (prefs.size) state.size = PC.clamp(prefs.size, MIN_SIZE, MAX_SIZE);

        dom.sizeSlider.value = String(state.size);
        dom.sizeReadout.textContent = `${state.size}×${state.size}`;
        dom.difficultySeg.querySelectorAll('button').forEach((btn) => {
            btn.classList.toggle('active', btn.dataset.value === state.difficulty);
            btn.addEventListener('click', () => setDifficulty(btn.dataset.value));
        });
        dom.sizeSlider.addEventListener('change', (ev) => setSize(ev.target.value));

        dom.newGameBtn.addEventListener('click', startNewGame);
        dom.resetBtn.addEventListener('click', resetPath_action);
        dom.revealBtn.addEventListener('click', toggleReveal);

        dom.board.classList.add('drag-board');
        dom.board.addEventListener('pointerdown', onPointerDown);
        dom.board.addEventListener('pointermove', onPointerMove);
        dom.board.addEventListener('pointerup', onPointerEnd);
        dom.board.addEventListener('pointercancel', onPointerEnd);
        // Don't let the browser kick in its own touch behaviours (scroll,
        // long-press) while the player is drawing — we already opt out of
        // panning via touch-action: manipulation on `.board-svg`, but
        // belt-and-braces this for older browsers.
        dom.board.addEventListener('contextmenu', (ev) => ev.preventDefault());

        state.timer = PC.timer(dom.timer);
        startNewGame();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
