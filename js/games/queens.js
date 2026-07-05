/**
 * Queens — gameplay + SVG rendering.
 *
 * Puzzle generation lives in `js/generators/queens.js` and is exposed
 * via `window.PuzzleGenerators.queens(size, difficulty, seed, onProgress)`.
 *
 * Puzzle JSON shape:
 *   {
 *     id:         string,
 *     game:       'queens',
 *     size:       N,
 *     difficulty: 'easy' | 'medium' | 'hard',
 *     regions:    int[N][N],          // regions[r][c] ∈ [0, N-1]
 *     solution:   int[N],             // solution[r] = column of queen
 *     stats?:     { ... },            // generator bookkeeping
 *   }
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const REGION_COLORS = [
        '#FF8888', '#FFB366', '#FFDD33', '#66DD66',
        '#7799FF', '#BB77DD', '#FF88CC', '#DD8855',
        '#88DDDD', '#DDAA77', '#99BB99', '#CCAAFF',
    ];

    const BOARD_SIZE = 480; // logical board area; SVG viewBox adds padding for outer stroke
    const STATES = { EMPTY: 0, MARK: 1, QUEEN: 2 };
    const STATE_CYCLE = [STATES.EMPTY, STATES.MARK, STATES.QUEEN]; // click order

    // Delay before red violation slashes appear after a placement change.
    // Matches the tk backup's "don't pester the player while they're still
    // cycling cells" behaviour.
    const VIOLATION_DELAY_MS = 800;

    // -----------------------------------------------------------------
    // Puzzle generation (thin wrapper around the async generator).
    //
    // Mirrors Tango's shape: the generator drives a determinate-friendly
    // progress callback, the game just adapts that into the shared
    // `PC.progress` UI.
    // -----------------------------------------------------------------

    async function generatePuzzle(size, difficulty, seed) {
        const progress = PC.progress;
        const onProgress = progress
            ? async (fraction) => {
                progress.setFraction(fraction);
                await progress.waitNextPaint();
            }
            : null;
        return window.PuzzleGenerators.queens(size, difficulty, seed, onProgress);
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,                   // current puzzle JSON
        placements: null,               // int[N][N] of STATES.*
        won: false,

        // Two layers of violation state:
        //   `violations` / `conflictPairs`           — recomputed instantly,
        //                                              used to decide win.
        //   `displayedViolations` / `displayedPairs` — what the UI shows,
        //                                              committed only after
        //                                              VIOLATION_DELAY_MS of
        //                                              no further clicks.
        violations: null,
        violationGroups: [],        // [{ kind, cells }] for partial refresh
        conflictPairs: 0,
        displayedViolations: null,
        displayedPairs: 0,
        violationTimer: null,
    };

    // The shell owns difficulty / size / revealed / timer.
    let shell = null;

    // Active pointer gesture. Modes:
    //   'mark'           — started on an empty cell. The starting cell
    //                      was already flipped to × at pointerdown time
    //                      (a tap-on-empty does the same thing). Every
    //                      subsequent empty cell the finger enters also
    //                      becomes ×.
    //   'unmark-pending' — started on ×. Ambiguous: could be a tap that
    //                      wants × → ♛, or a drag that wants to erase ×s.
    //                      We defer until the pointer leaves the start;
    //                      the first move commits us into 'unmark'.
    //   'unmark'         — committed drag-erase. The starting cell has
    //                      been cleared to empty and every × the finger
    //                      passes over gets cleared too.
    //   'tap'            — started on ♛. Pure tap: cycle only if the
    //                      release lands back on the same cell.
    let dragState = null;

    function emptyViolationGrid(N) {
        return Array.from({ length: N }, () => new Array(N).fill(false));
    }

    function ensurePlacementsForCurrent() {
        const N = state.puzzle.size;
        state.placements = Array.from({ length: N }, () => new Array(N).fill(STATES.EMPTY));
        state.violations = emptyViolationGrid(N);
        state.violationGroups = [];
        state.conflictPairs = 0;
        state.displayedViolations = emptyViolationGrid(N);
        state.displayedPairs = 0;
        cancelViolationTimer();
        state.won = false;
    }

    function cancelViolationTimer() {
        if (state.violationTimer) {
            clearTimeout(state.violationTimer);
            state.violationTimer = null;
        }
    }

    function commitViolationDisplay() {
        state.violationTimer = null;
        if (!state.violations) return;
        state.displayedViolations = state.violations.map((row) => row.slice());
        state.displayedPairs = state.conflictPairs;
        repaintSymbols();
        updateStatusRow();
    }

    // -----------------------------------------------------------------
    // Rules
    // -----------------------------------------------------------------

    /**
     * Recompute violations from current placements. Two views are
     * produced: a cell-level `flagged` grid (used for the win check and
     * the 800ms-debounced full display), and a list of `groups` where
     * each group is a pair of queens that breaks at least one rule. The
     * group view lets the partial-refresh logic hide only the conflicts
     * that the latest toggle could possibly have affected.
     *
     * Returns the list of queen positions so callers can avoid scanning
     * the board twice.
     */
    function recomputeViolations() {
        const N = state.puzzle.size;
        const regions = state.puzzle.regions;
        const queens = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.placements[r][c] === STATES.QUEEN) {
                    queens.push([r, c]);
                }
            }
        }
        const flagged = emptyViolationGrid(N);
        const groups = [];

        // A "conflict pair" is two queens that violate ANY rule (a pair
        // that breaks multiple rules still counts as one).
        for (let i = 0; i < queens.length; i++) {
            const [r1, c1] = queens[i];
            for (let j = i + 1; j < queens.length; j++) {
                const [r2, c2] = queens[j];
                const sameRow = r1 === r2;
                const sameCol = c1 === c2;
                const adj8 = Math.abs(r1 - r2) <= 1 && Math.abs(c1 - c2) <= 1;
                const sameRegion = regions[r1][c1] === regions[r2][c2];
                if (sameRow || sameCol || adj8 || sameRegion) {
                    flagged[r1][c1] = true;
                    flagged[r2][c2] = true;
                    groups.push({ kind: 'pair', cells: [[r1, c1], [r2, c2]] });
                }
            }
        }
        state.violations = flagged;
        state.violationGroups = groups;
        state.conflictPairs = groups.length;
        return queens;
    }

    /**
     * A pair-conflict between two queens is "owned by" a toggle at
     * (r0, c0) iff (r0, c0) is one of the two queens involved. The
     * conflict between two OTHER queens cannot change as a result of
     * the toggle, so it stays on screen.
     */
    function isGroupOwnedBy(group, r0, c0) {
        return group.cells.some(([r, c]) => r === r0 && c === c0);
    }

    function checkWin() {
        const N = state.puzzle.size;
        // Count queens from the flagged grid's source (state.placements)
        // — caller must have run `recomputeViolations` already.
        let queenCount = 0;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.placements[r][c] === STATES.QUEEN) queenCount += 1;
            }
        }
        return queenCount === N && state.conflictPairs === 0;
    }

    /**
     * Refresh the displayed-violation overlay after a toggle at (r0, c0).
     * Conflicts whose group is NOT owned by the toggle stay visible
     * immediately. Conflicts that ARE owned are hidden for
     * VIOLATION_DELAY_MS, after which commitViolationDisplay flushes
     * the full set.
     */
    function scheduleViolationRefresh(r0, c0) {
        cancelViolationTimer();
        const N = state.puzzle.size;
        const visible = emptyViolationGrid(N);
        let count = 0;
        for (const g of state.violationGroups || []) {
            if (isGroupOwnedBy(g, r0, c0)) continue;
            count += 1;
            for (const [r, c] of g.cells) visible[r][c] = true;
        }
        state.displayedViolations = visible;
        state.displayedPairs = count;
        state.violationTimer = setTimeout(commitViolationDisplay, VIOLATION_DELAY_MS);
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    // Only the board needs a long-lived ref here — the shell owns the
    // toolbar / status row DOM.
    let board = null;

    function regionColor(idx) {
        return REGION_COLORS[idx % REGION_COLORS.length];
    }

    function cellRect(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { x: c * cs, y: r * cs, size: cs };
    }

    function renderBoard() {
        const N = state.puzzle.size;
        const regions = state.puzzle.regions;
        const svg = board;
        // Clear
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        const cs = BOARD_SIZE / N;

        // Layer: cell backgrounds (colored by region)
        const bgGroup = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const rect = PC.svgEl('rect', {
                    class: 'cell-bg',
                    x, y, width: size, height: size,
                    fill: regionColor(regions[r][c]),
                });
                bgGroup.appendChild(rect);
            }
        }
        svg.appendChild(bgGroup);

        // Layer: region borders (thick lines between differing regions and
        // around the outer perimeter — same stroke width everywhere). The
        // SVG viewBox has 3px of padding so the outer stroke isn't clipped.
        const borderGroup = PC.svgEl('g', { class: 'region-borders' });
        const addBorder = (x1, y1, x2, y2) => {
            borderGroup.appendChild(PC.svgEl('line', {
                class: 'region-border', x1, y1, x2, y2,
            }));
        };
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const rid = regions[r][c];
                const { x, y, size } = cellRect(N, r, c);
                if (r === 0 || regions[r - 1][c] !== rid) {
                    addBorder(x, y, x + size, y);
                }
                if (c === 0 || regions[r][c - 1] !== rid) {
                    addBorder(x, y, x, y + size);
                }
                if (r === N - 1) addBorder(x, y + size, x + size, y + size);
                if (c === N - 1) addBorder(x + size, y, x + size, y + size);
            }
        }
        svg.appendChild(borderGroup);

        // Layer: symbols (queen / mark) + violations + reveal overlay
        const symbolGroup = PC.svgEl('g', { class: 'symbols' });
        symbolGroup.setAttribute('id', 'symbols');
        svg.appendChild(symbolGroup);

        // Layer: invisible click targets (placed last so they capture events)
        const hitGroup = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const hit = PC.svgEl('rect', {
                    class: 'cell-hover',
                    x, y, width: size, height: size,
                    'data-r': r,
                    'data-c': c,
                });
                hitGroup.appendChild(hit);
            }
        }
        svg.appendChild(hitGroup);

        repaintSymbols();
    }

    function repaintSymbols() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const group = board.querySelector('#symbols');
        while (group.firstChild) group.removeChild(group.firstChild);

        const symbolFont = Math.max(14, Math.floor(cs * 0.55));
        const markFont = Math.max(12, Math.floor(cs * 0.45));

        // Player symbols
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const s = state.placements[r][c];
                if (s === STATES.EMPTY) continue;
                const cx = c * cs + cs / 2;
                const cy = r * cs + cs / 2;
                if (s === STATES.QUEEN) {
                    const cls = 'symbol queen' + (state.won ? ' victory' : '');
                    const text = PC.svgEl('text', {
                        class: cls,
                        x: cx, y: cy,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.10em',
                        'font-size': symbolFont,
                    });
                    text.textContent = '♛';
                    group.appendChild(text);
                } else if (s === STATES.MARK) {
                    const text = PC.svgEl('text', {
                        class: 'symbol mark',
                        x: cx, y: cy,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.04em',
                        'font-size': markFont,
                    });
                    text.textContent = '×';
                    group.appendChild(text);
                }
            }
        }

        // Violations (read from the *displayed* buffer, which is debounced)
        const vis = state.displayedViolations;
        if (vis) {
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (!vis[r][c]) continue;
                    const inset = Math.max(4, cs * 0.18);
                    const x1 = c * cs + inset;
                    const y1 = r * cs + inset;
                    const x2 = (c + 1) * cs - inset;
                    const y2 = (r + 1) * cs - inset;
                    group.appendChild(PC.svgEl('line', {
                        class: 'violation-line',
                        x1, y1, x2, y2,
                    }));
                    group.appendChild(PC.svgEl('line', {
                        class: 'violation-line',
                        x1: x2, y1: y1, x2: x1, y2: y2,
                    }));
                }
            }
        }

        // Solution overlay (Reveal). Always shown — even when the cell has a
        // player mark or queen — but kept tiny in the corner so it never
        // collides with the player's main symbol (which is centered).
        if (shell.revealed && state.puzzle && state.puzzle.solution) {
            const sol = state.puzzle.solution;
            const hintFont = Math.max(9, Math.floor(cs * 0.24));
            for (let r = 0; r < N; r++) {
                const c = sol[r];
                const text = PC.svgEl('text', {
                    class: 'symbol reveal-hint',
                    x: c * cs + cs * 0.15,
                    y: r * cs + cs * 0.18,
                    'text-anchor': 'middle',
                    'dominant-baseline': 'middle',
                    dy: '0.10em',
                    'font-size': hintFont,
                });
                text.textContent = '♛';
                group.appendChild(text);
            }
        }
    }

    function updateStatusRow() {
        shell.setViolationCount(state.displayedPairs);
        shell.setWin(state.won);
    }

    // -----------------------------------------------------------------
    // Event handlers
    // -----------------------------------------------------------------

    // Transition a single cell to the given state. Only ♛ transitions
    // can create or dissolve a violation / win, so pure × toggles skip
    // the recompute — that keeps a fast drag-mark from paying the O(N²)
    // scan on every intermediate cell.
    function applyCellState(r, c, next) {
        if (!state.puzzle || state.won) return;
        const cur = state.placements[r][c];
        if (cur === next) return;
        state.placements[r][c] = next;

        const queenInvolved = cur === STATES.QUEEN || next === STATES.QUEEN;
        if (queenInvolved) {
            recomputeViolations();
            if (checkWin() && !state.won) {
                state.won = true;
                cancelViolationTimer();
                state.displayedViolations = emptyViolationGrid(state.puzzle.size);
                state.displayedPairs = 0;
                shell.markSolved();
                repaintSymbols();
                updateStatusRow();
                return;
            }
            // Show unrelated conflicts immediately; debounce the ones
            // owned by this toggle for VIOLATION_DELAY_MS so the red
            // slashes don't flash distractingly while the player is
            // still cycling through states in the same row / col /
            // region / neighbourhood.
            scheduleViolationRefresh(r, c);
        }
        repaintSymbols();
        updateStatusRow();
    }

    function cycleCell(r, c) {
        if (!state.puzzle || state.won) return;
        const cur = state.placements[r][c];
        const idx = STATE_CYCLE.indexOf(cur);
        const next = STATE_CYCLE[(idx + 1) % STATE_CYCLE.length];
        applyCellState(r, c, next);
    }

    // Map a pointer event to a board cell using the SVG viewBox math.
    // Mirrors Zip's helper: the playable area occupies viewBox coords
    // (0..BOARD_SIZE, 0..BOARD_SIZE) inside a 486×486 SVG with 3px
    // padding on each side.
    function eventToCell(ev) {
        if (!state.puzzle) return null;
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

    function onPointerDown(ev) {
        if (!state.puzzle || state.won) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        if (dragState) return; // ignore secondary pointers mid-gesture
        const cell = eventToCell(ev);
        if (!cell) return;
        const [r, c] = cell;
        const cur = state.placements[r][c];

        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }

        let mode;
        if (cur === STATES.EMPTY) {
            // Tap-on-empty is already "→ ×" per the cycle, so we can
            // apply immediately and keep painting subsequent cells.
            applyCellState(r, c, STATES.MARK);
            mode = 'mark';
        } else if (cur === STATES.MARK) {
            // Ambiguous — could be a tap wanting × → ♛, or a drag
            // wanting to erase ×s. Defer until the pointer leaves this
            // cell; see the promotion logic in onPointerMove.
            mode = 'unmark-pending';
        } else {
            // Started on ♛ — behave like a click (cycle only if the
            // release lands here).
            mode = 'tap';
        }
        dragState = {
            pointerId: ev.pointerId, mode,
            startR: r, startC: c, lastR: r, lastC: c,
        };
    }

    function onPointerMove(ev) {
        if (!dragState || ev.pointerId !== dragState.pointerId) return;
        const cell = eventToCell(ev);
        if (!cell) return;
        const [r, c] = cell;
        if (r === dragState.lastR && c === dragState.lastC) return;
        dragState.lastR = r; dragState.lastC = c;

        // First move away from the start commits an unmark-pending
        // gesture into a real drag-erase: clear the starting × and
        // switch modes so the current cell (and subsequent ones) all
        // go through the same rule.
        if (dragState.mode === 'unmark-pending') {
            applyCellState(dragState.startR, dragState.startC, STATES.EMPTY);
            dragState.mode = 'unmark';
        }

        if (dragState.mode === 'mark'
            && state.placements[r][c] === STATES.EMPTY) {
            applyCellState(r, c, STATES.MARK);
        } else if (dragState.mode === 'unmark'
            && state.placements[r][c] === STATES.MARK) {
            applyCellState(r, c, STATES.EMPTY);
        }
    }

    function onPointerUp(ev) {
        if (!dragState || ev.pointerId !== dragState.pointerId) return;
        const cell = eventToCell(ev);
        const { mode, startR, startC, pointerId } = dragState;
        dragState = null;
        try { board.releasePointerCapture(pointerId); } catch (_) { /* ignore */ }
        // 'tap' (started on ♛) and 'unmark-pending' (started on × but
        // never left) both resolve as a plain cycle if the release
        // lands on the starting cell. Everything else has already been
        // committed by the move handler.
        const tapLike = mode === 'tap' || mode === 'unmark-pending';
        if (tapLike
            && cell && cell[0] === startR && cell[1] === startC) {
            cycleCell(startR, startC);
        }
    }

    async function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        ensurePlacementsForCurrent();
        renderBoard();
        updateStatusRow();
    }

    function resetPlacements() {
        if (!state.puzzle) return;
        ensurePlacementsForCurrent();
        state.won = false;
        repaintSymbols();
        updateStatusRow();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'queens',
            difficulty: { default: 'medium' },
            size: { kind: 'slider', min: 5, max: 12, default: 8 },
            onNewGame: startNewGame,
            onReset: resetPlacements,
            onReveal: repaintSymbols,
        });
        board = shell.dom.board;
        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerUp);
        board.addEventListener('pointercancel', onPointerUp);
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());
        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
