/**
 * Tango — gameplay + SVG rendering.
 *
 * Puzzle generation lives in `js/generators/tango.js` and is exposed via
 * `window.PuzzleGenerators.tango(size, difficulty, seed)`. The shape of
 * the puzzle object returned by the generator is:
 *
 *   {
 *     id:         string,
 *     game:       'tango',
 *     size:       N,                 // 6, 8 or 10
 *     difficulty: 'easy' | 'medium' | 'hard',
 *     prefilled:  int[N][N],         // 0 empty, 1 sun, 2 moon (locked)
 *     walls: [
 *       { r1, c1, r2, c2, kind }     // kind: 'same' (=) | 'diff' (×)
 *     ],                             // (r1,c1) lex-< (r2,c2), 4-adjacent
 *     solution:   int[N][N],         // 1 sun, 2 moon (always full)
 *   }
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const BOARD_SIZE = 480;
    const STATES = { EMPTY: 0, SUN: 1, MOON: 2 };
    const STATE_CYCLE = [STATES.EMPTY, STATES.SUN, STATES.MOON];

    const SYMBOL = {
        [STATES.SUN]: '☀',
        [STATES.MOON]: '☾',
    };

    const VIOLATION_DELAY_MS = 800;

    function generatePuzzle(size, difficulty, seed) {
        return window.PuzzleGenerators.tango(size, difficulty, seed);
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        placements: null,           // int[N][N] of STATES.*; for prefilled cells stays 0
        won: false,

        violations: null,           // bool[N][N] (used for win check + full-flush display)
        violationGroups: [],        // [{ kind, key, cells }] for partial refresh
        conflictPairs: 0,
        displayedViolations: null,
        displayedPairs: 0,
        violationTimer: null,

        hint: null,                 // active hint object from PuzzleSolvers.tango.nextDeduction
        hintBanner: null,           // DOM node for the hint message banner
        hintButton: null,           // DOM node for the hint button

        // -- Hint continuity bookkeeping --
        // The most recent hint we showed the player, retained until its
        // target cell is filled with the suggested value. Even if the
        // player ignores it and works on something else, we keep
        // re-suggesting it whenever no clearly-easier (lower-tier) hint
        // exists.
        pendingHint: null,          // { cell:[r,c], value, reasonKind, tier } | null
        // The player's last placement / cycle. Used to rank otherwise-
        // tied candidate hints by similarity (same row/col, same wall
        // cluster, same assumption line, etc.) so the next hint feels
        // continuous with what the player just did.
        lastMove: null,             // { cell:[r,c], value, reasonKind } | null
        // Cached wall-graph connected components for the current puzzle,
        // used by similarityScore for T-wall locality matching.
        wallIndex: null,
    };

    let shell = null;

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
        clearHint();
        state.pendingHint = null;
        state.lastMove = null;
        const solver = window.PuzzleSolvers && window.PuzzleSolvers.tango;
        state.wallIndex = solver && solver.buildWallIndex
            ? solver.buildWallIndex(state.puzzle.walls)
            : null;
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

    /** Effective symbol at a cell (prefilled if locked, otherwise player). */
    function effective(r, c) {
        const e = state.puzzle.prefilled[r][c];
        return e !== STATES.EMPTY ? e : state.placements[r][c];
    }

    function isPrefilled(r, c) {
        return state.puzzle.prefilled[r][c] !== STATES.EMPTY;
    }

    // -----------------------------------------------------------------
    // Rules
    // -----------------------------------------------------------------

    /**
     * Recompute violations from the current placements. As well as the
     * cell-level `flagged` grid (used for the win check + the full
     * 800ms-debounced display), we also build a list of `groups` so the
     * partial-refresh logic can hide only the conflicts that the latest
     * edit could possibly have affected.
     *
     * Group kinds:
     *   'row'    row count overflow at row R
     *   'col'    col count overflow at col C
     *   'rowRun' three-in-a-row horizontally in row R
     *   'colRun' three-in-a-row vertically  in col C
     *   'wall'   broken `=` / `×` wall between two cells
     */
    function recomputeViolations() {
        const N = state.puzzle.size;
        const half = N / 2;
        const flagged = emptyViolationGrid(N);
        const groups = [];

        function flag(r, c) { flagged[r][c] = true; }

        // Counts per row and column.
        const rowSun = new Array(N).fill(0);
        const rowMoon = new Array(N).fill(0);
        const colSun = new Array(N).fill(0);
        const colMoon = new Array(N).fill(0);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = effective(r, c);
                if (v === STATES.SUN) { rowSun[r]++; colSun[c]++; }
                else if (v === STATES.MOON) { rowMoon[r]++; colMoon[c]++; }
            }
        }

        // Row / column count overflow.
        for (let r = 0; r < N; r++) {
            if (rowSun[r] > half) {
                const cells = [];
                for (let c = 0; c < N; c++) {
                    if (effective(r, c) === STATES.SUN) { cells.push([r, c]); flag(r, c); }
                }
                groups.push({ kind: 'row', key: r, cells });
            }
            if (rowMoon[r] > half) {
                const cells = [];
                for (let c = 0; c < N; c++) {
                    if (effective(r, c) === STATES.MOON) { cells.push([r, c]); flag(r, c); }
                }
                groups.push({ kind: 'row', key: r, cells });
            }
        }
        for (let c = 0; c < N; c++) {
            if (colSun[c] > half) {
                const cells = [];
                for (let r = 0; r < N; r++) {
                    if (effective(r, c) === STATES.SUN) { cells.push([r, c]); flag(r, c); }
                }
                groups.push({ kind: 'col', key: c, cells });
            }
            if (colMoon[c] > half) {
                const cells = [];
                for (let r = 0; r < N; r++) {
                    if (effective(r, c) === STATES.MOON) { cells.push([r, c]); flag(r, c); }
                }
                groups.push({ kind: 'col', key: c, cells });
            }
        }

        // Three-in-a-row in rows (each maximal run of length >= 3 counts once).
        for (let r = 0; r < N; r++) {
            let runStart = 0;
            let runVal = effective(r, 0);
            for (let c = 1; c <= N; c++) {
                const v = c < N ? effective(r, c) : -1;
                if (v !== runVal) {
                    const runLen = c - runStart;
                    if (runVal !== STATES.EMPTY && runLen >= 3) {
                        const cells = [];
                        for (let k = runStart; k < c; k++) { cells.push([r, k]); flag(r, k); }
                        groups.push({ kind: 'rowRun', key: r, cells });
                    }
                    runStart = c;
                    runVal = v;
                }
            }
        }
        for (let c = 0; c < N; c++) {
            let runStart = 0;
            let runVal = effective(0, c);
            for (let r = 1; r <= N; r++) {
                const v = r < N ? effective(r, c) : -1;
                if (v !== runVal) {
                    const runLen = r - runStart;
                    if (runVal !== STATES.EMPTY && runLen >= 3) {
                        const cells = [];
                        for (let k = runStart; k < r; k++) { cells.push([k, c]); flag(k, c); }
                        groups.push({ kind: 'colRun', key: c, cells });
                    }
                    runStart = r;
                    runVal = v;
                }
            }
        }

        // Wall constraints.
        for (const w of state.puzzle.walls) {
            const a = effective(w.r1, w.c1);
            const b = effective(w.r2, w.c2);
            if (a === STATES.EMPTY || b === STATES.EMPTY) continue;
            const broken = (w.kind === 'same' && a !== b)
                        || (w.kind === 'diff' && a === b);
            if (broken) {
                flag(w.r1, w.c1);
                flag(w.r2, w.c2);
                groups.push({
                    kind: 'wall',
                    key: `${w.r1},${w.c1}-${w.r2},${w.c2}`,
                    cells: [[w.r1, w.c1], [w.r2, w.c2]],
                });
            }
        }

        state.violations = flagged;
        state.violationGroups = groups;
        state.conflictPairs = groups.length;
    }

    /**
     * Is the given conflict group "owned" by a toggle at (r0, c0)? A
     * group is owned when toggling that cell could possibly have
     * changed it, which is exactly the set of constraints that include
     * the cell: its row, its column, and (for wall groups) the cell
     * itself.
     */
    function isGroupOwnedBy(group, r0, c0) {
        if (group.kind === 'row' || group.kind === 'rowRun') return group.key === r0;
        if (group.kind === 'col' || group.kind === 'colRun') return group.key === c0;
        if (group.kind === 'wall') {
            return group.cells.some(([r, c]) => r === r0 && c === c0);
        }
        return false;
    }

    function isFullyFilled() {
        const N = state.puzzle.size;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (effective(r, c) === STATES.EMPTY) return false;
            }
        }
        return true;
    }

    /**
     * Win check assumes `recomputeViolations` has already been called for
     * the current placements; callers handle the recompute themselves
     * so we don't pay for it twice.
     */
    function checkWin() {
        return isFullyFilled() && state.conflictPairs === 0;
    }

    /**
     * Recompute the displayed-violation overlay after a toggle at
     * (r0, c0). Conflicts whose constraint group is NOT owned by the
     * toggle stay visible immediately — they can't have changed.
     * Conflicts owned by the toggle are hidden, and the full set is
     * flushed via commitViolationDisplay after VIOLATION_DELAY_MS.
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

    let board = null;

    function cellRect(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { x: c * cs, y: r * cs, size: cs };
    }

    function renderBoard() {
        const N = state.puzzle.size;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        const cs = BOARD_SIZE / N;

        // Layer: cell backgrounds (light fill; prefilled get a darker tint).
        const bgGroup = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const cls = 'cell-bg' + (isPrefilled(r, c) ? ' prefilled' : '');
                bgGroup.appendChild(PC.svgEl('rect', {
                    class: cls,
                    x, y, width: size, height: size,
                    fill: isPrefilled(r, c) ? '#e6e8ee' : '#ffffff',
                }));
            }
        }
        svg.appendChild(bgGroup);

        // Layer: outer frame (same stroke style as Queens' region borders).
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

        // Layer: symbols + violations + reveal hint (rebuilt every repaint).
        const symbolGroup = PC.svgEl('g', { class: 'symbols' });
        symbolGroup.setAttribute('id', 'symbols');
        svg.appendChild(symbolGroup);

        // Layer: wall badges (=/× glyphs sitting directly on the cell
        // boundary; no background — just the symbol on top of the grid).
        const wallGroup = PC.svgEl('g', { class: 'walls' });
        const glyphSize = Math.max(13, Math.floor(cs * 0.42));
        for (const w of state.puzzle.walls) {
            const x = ((w.c1 + w.c2 + 1) * cs) / 2;
            const y = ((w.r1 + w.r2 + 1) * cs) / 2;
            const t = PC.svgEl('text', {
                class: 'wall-glyph',
                x, y,
                'text-anchor': 'middle',
                'dominant-baseline': 'middle',
                dy: '0.04em',
                'font-size': glyphSize,
            });
            t.textContent = w.kind === 'same' ? '=' : '×';
            wallGroup.appendChild(t);
        }
        svg.appendChild(wallGroup);

        // Layer: invisible click targets (last, so they sit on top).
        const hitGroup = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                if (isPrefilled(r, c)) continue; // prefilled cells aren't clickable
                hitGroup.appendChild(PC.svgEl('rect', {
                    class: 'cell-hover',
                    x, y, width: size, height: size,
                    'data-r': r,
                    'data-c': c,
                }));
            }
        }
        svg.appendChild(hitGroup);

        repaintSymbols();
        applyHintHighlights();
    }

    function repaintSymbols() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const group = board.querySelector('#symbols');
        while (group.firstChild) group.removeChild(group.firstChild);

        const symbolFont = Math.max(16, Math.floor(cs * 0.55));

        // Symbols (prefilled + player)
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = effective(r, c);
                if (v === STATES.EMPTY) continue;
                const cx = c * cs + cs / 2;
                const cy = r * cs + cs / 2;
                const symbolKind = v === STATES.SUN ? 'sun' : 'moon';
                const lockedClass = isPrefilled(r, c) ? ' prefilled' : '';
                const text = PC.svgEl('text', {
                    class: `symbol ${symbolKind}${lockedClass}`,
                    x: cx, y: cy,
                    'text-anchor': 'middle',
                    'dominant-baseline': 'middle',
                    dy: '0.12em',
                    'font-size': symbolFont,
                });
                text.textContent = SYMBOL[v];
                group.appendChild(text);
            }
        }

        // Chain ghosts for L2/L3/L4 hints — render the bad-hypothesis
        // value forced into each cell along the contradiction chain
        // as a static faded-red glyph. The hint-target cell carries
        // an amber background (set by applyHintHighlights), which is
        // what visually distinguishes step 1 from the rest. A tiny
        // step-order badge in the top-right corner makes the
        // derivation order explicit; top-left is left for the reveal
        // overlay.
        if (state.hint && state.hint.chainPlacements && state.hint.chainPlacements.length > 0) {
            const stepFont = Math.max(9, Math.floor(cs * 0.22));
            for (let i = 0; i < state.hint.chainPlacements.length; i++) {
                const { cell, value } = state.hint.chainPlacements[i];
                const [r, c] = cell;
                if (effective(r, c) !== STATES.EMPTY) continue;
                const cx = c * cs + cs / 2;
                const cy = r * cs + cs / 2;
                const symbolKind = value === STATES.SUN ? 'sun' : 'moon';
                const ghost = PC.svgEl('text', {
                    class: `symbol ${symbolKind} hint-ghost`,
                    x: cx, y: cy,
                    'text-anchor': 'middle',
                    'dominant-baseline': 'middle',
                    dy: '0.12em',
                    'font-size': symbolFont,
                });
                ghost.textContent = SYMBOL[value];
                group.appendChild(ghost);

                // Step-order badge (top-right corner).
                const stepLabel = PC.svgEl('text', {
                    class: 'symbol hint-step',
                    x: c * cs + cs * 0.84,
                    y: r * cs + cs * 0.20,
                    'text-anchor': 'middle',
                    'dominant-baseline': 'middle',
                    'font-size': stepFont,
                });
                stepLabel.textContent = String(i + 1);
                group.appendChild(stepLabel);
            }
        }

        // Violations (read from the debounced display buffer)
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

        // Reveal: tiny solution symbol in the top-left corner of each
        // *player-editable* cell. Prefilled cells already display the
        // correct answer, so they don't need the hint.
        if (shell.revealed && state.puzzle && state.puzzle.solution) {
            const sol = state.puzzle.solution;
            const hintFont = Math.max(9, Math.floor(cs * 0.22));
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (isPrefilled(r, c)) continue;
                    const text = PC.svgEl('text', {
                        class: 'symbol reveal-hint',
                        x: c * cs + cs * 0.16,
                        y: r * cs + cs * 0.18,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.12em',
                        'font-size': hintFont,
                    });
                    text.textContent = SYMBOL[sol[r][c]];
                    group.appendChild(text);
                }
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

    function cycleCell(r, c) {
        if (!state.puzzle || state.won) return;
        if (isPrefilled(r, c)) return;
        // The hint banner sits below the board now, so touching any cell
        // dismisses it without misleading the player. (pendingHint /
        // lastMove are intentionally NOT cleared here — clearHint only
        // hides the displayed banner; the continuity state survives.)
        clearHint();
        const cur = state.placements[r][c];
        const idx = STATE_CYCLE.indexOf(cur);
        const newVal = STATE_CYCLE[(idx + 1) % STATE_CYCLE.length];
        state.placements[r][c] = newVal;

        // Update hint-continuity bookkeeping. If the player's cycle
        // landed on the value the pendingHint suggested for this cell,
        // the hint is "completed" and we drop it. We also forward the
        // hint's rule-kind into lastMove so the next similarity ranking
        // can prefer same-rule candidates.
        let lastMoveReasonKind = null;
        if (state.pendingHint
            && state.pendingHint.cell[0] === r
            && state.pendingHint.cell[1] === c
            && state.pendingHint.value === newVal) {
            lastMoveReasonKind = state.pendingHint.reasonKind || null;
            state.pendingHint = null;
        }
        state.lastMove = { cell: [r, c], value: newVal, reasonKind: lastMoveReasonKind };

        recomputeViolations();
        if (checkWin() && !state.won) {
            state.won = true;
            cancelViolationTimer();
            state.displayedViolations = emptyViolationGrid(state.puzzle.size);
            state.displayedPairs = 0;
            clearHint();
            shell.markSolved();
            repaintSymbols();
            updateStatusRow();
            return;
        }

        scheduleViolationRefresh(r, c);
        repaintSymbols();
        updateStatusRow();
    }

    function onBoardClick(ev) {
        const target = ev.target.closest('rect.cell-hover');
        if (!target) return;
        const r = parseInt(target.getAttribute('data-r'), 10);
        const c = parseInt(target.getAttribute('data-c'), 10);
        cycleCell(r, c);
    }

    // -----------------------------------------------------------------
    // Hints
    //
    // state.hint shape (when active):
    //   {
    //     mode: 'error' | 'deduction' | 'noHint',
    //     // Common rendering data:
    //     targetCells: [[r, c], ...],     // amber-highlighted target
    //     contextCells: [[r, c], ...],    // soft-highlighted background
    //     violationCells: [[r, c], ...],  // red-highlighted breakage
    //     chainPlacements: [{cell,value}, ...] | null,
    //     badgeText: '',
    //     // Mode-specific source fields used by renderHintBannerFromState
    //     // to recompute bannerText each render (so a locale change
    //     // refreshes the banner without recomputing the hint itself):
    //     reason:    object   // 'deduction' only
    //     wrongCount:integer  // 'error' only
    //     filterTactic: 'L3' | null  // 'noHint' only
    //     filterTactics:['L1',...]   // 'noHint' only
    //   }
    // -----------------------------------------------------------------

    /**
     * Optional URL filter for which tiers count as a hint. Use
     * `?hintMin=L3` to skip L1/L2 (so debugging L3+ doesn't require
     * actually getting stuck), `?hintMin=L4` to only return L4, etc.
     * Defaults to all four tiers.
     */
    function getHintTierFilter() {
        const params = new URLSearchParams(window.location.search);
        const min = (params.get('hintMin') || '').toUpperCase();
        const all = ['L1', 'L2', 'L3', 'L4'];
        const idx = all.indexOf(min);
        return idx > 0 ? all.slice(idx) : all;
    }

    /**
     * Compose the `filled` grid we feed to the solver for hinting.
     * Includes prefill plus any player placements that already match
     * the solution — that way wrong guesses can't fool the solver into
     * walking off into nonsense, but correct progress still counts.
     */
    function composeFilledForHint() {
        const N = state.puzzle.size;
        const sol = state.puzzle.solution;
        const out = Array.from({ length: N }, () => new Array(N).fill(STATES.EMPTY));
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const pre = state.puzzle.prefilled[r][c];
                if (pre !== STATES.EMPTY) { out[r][c] = pre; continue; }
                const pla = state.placements[r][c];
                if (pla !== STATES.EMPTY && pla === sol[r][c]) out[r][c] = pla;
            }
        }
        return out;
    }

    function findWrongCells() {
        const N = state.puzzle.size;
        const sol = state.puzzle.solution;
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.puzzle.prefilled[r][c] !== STATES.EMPTY) continue;
                const pla = state.placements[r][c];
                if (pla !== STATES.EMPTY && pla !== sol[r][c]) out.push([r, c]);
            }
        }
        return out;
    }

    // Hint-banner UI strings. English is the active locale; Chinese
    // strings are preserved so a future commit can wire a UI toggle
    // that flips PuzzleCommon.i18n.locale without re-translating.
    const HINT_UI_TEXTS = {
        en: {
            wrongOne: 'This highlighted cell does not match the unique solution — please reconsider.',
            wrongMany: (n) =>
                `These ${n} highlighted cells do not match the unique solution — please reconsider.`,
            noneFiltered: (min, list) =>
                `(hintMin=${min}) No ${list} deductions are available right now.`,
            noneAvail: 'There are no more cells that can be deduced.',
        },
        zh: {
            wrongOne: '高亮的這格與唯一解不符，請重新檢查。',
            wrongMany: (n) => `高亮的這 ${n} 格與唯一解不符，請重新檢查。`,
            noneFiltered: (min, list) => `（hintMin=${min}）目前沒有 ${list} 等級的推論可指。`,
            noneAvail: '目前已經沒有可推論的格子。',
        },
    };

    function uiTexts() {
        const loc = (PC.i18n && PC.i18n.locale) || 'en';
        return HINT_UI_TEXTS[loc] || HINT_UI_TEXTS.en;
    }

    function showHint() {
        if (!state.puzzle || state.won) return;
        // Toggle off if a hint is already showing.
        if (state.hint) { clearHint(); return; }

        // Priority 1: wrong placements. Tango is unique-solution, so any
        // cell that disagrees with the stored solution is provably bad.
        const wrong = findWrongCells();
        if (wrong.length > 0) {
            state.hint = {
                mode: 'error',
                targetCells: wrong,
                contextCells: [],
                violationCells: [],
                chainPlacements: null,
                wrongCount: wrong.length,
                badgeText: '',
            };
            renderHintBannerFromState();
            applyHintHighlights();
            return;
        }

        // Priority 2: regular deduction. Honours ?hintMin=L3 / =L4 for
        // testing higher tiers without grinding through L1 cells first.
        const tactics = getHintTierFilter();
        const filled = composeFilledForHint();
        const N = state.puzzle.size;
        const solver = window.PuzzleSolvers.tango;
        const result = solver.findLowestAvailableTier(filled, state.puzzle.walls, N, tactics);

        if (!result || result.deductions.length === 0) {
            state.hint = {
                mode: 'noHint',
                targetCells: [],
                contextCells: [],
                violationCells: [],
                chainPlacements: null,
                filterTactic: tactics.length < 4 ? tactics[0] : null,
                filterTactics: tactics,
                badgeText: '',
            };
            renderHintBannerFromState();
            applyHintHighlights();
            return;
        }

        const picked = pickHint(result.deductions, state.lastMove, state.pendingHint);

        // Remember this hint so we can re-suggest it on subsequent
        // calls until the player either fulfills it or a strictly
        // easier hint becomes available elsewhere.
        state.pendingHint = {
            cell: picked.cell,
            value: picked.value,
            reasonKind: picked.reason.kind,
            tier: picked.tier,
        };

        state.hint = {
            mode: 'deduction',
            targetCells: [picked.cell],
            contextCells: solver.reasonContextCells(picked.reason),
            violationCells: solver.reasonViolationCells(picked.reason),
            chainPlacements: solver.reasonChainPlacements(picked.reason),
            reason: picked.reason,
            // Never surface the L1/L2/L3/L4 tier in the banner — that
            // jargon is for the generator, not the player.
            badgeText: '',
        };
        renderHintBannerFromState();
        applyHintHighlights();
        repaintSymbols();
    }

    /**
     * Choose which of the (equally-low-tier) candidate deductions to
     * surface. The order of preference is:
     *
     *   1) pendingHint's cell, if still in the candidate list —
     *      "stubborn hint". The player previously saw this hint and
     *      hasn't completed it; we keep nudging them toward the same
     *      conclusion so they aren't whiplashed between unrelated
     *      suggestions every click.
     *      (Because `result.deductions` only contains the lowest
     *      available tier, this automatically defers to any new
     *      strictly-lower-tier hint that has opened up since.)
     *
     *   2) Otherwise, rank by similarityScore against `lastMove` —
     *      prefer same-line / same-wall-cluster / same-rule hints so
     *      the next suggestion feels like a natural follow-up.
     *
     *   3) Row-major tiebreak (first candidate with the best score
     *      wins, by virtue of iterating the list in order).
     */
    function pickHint(deductions, lastMove, pendingHint) {
        if (deductions.length === 0) return null;
        if (pendingHint) {
            const match = deductions.find((d) =>
                d.cell[0] === pendingHint.cell[0] && d.cell[1] === pendingHint.cell[1]);
            if (match) return match;
        }
        if (!lastMove) return deductions[0];
        let best = deductions[0];
        let bestScore = similarityScore(deductions[0], lastMove);
        for (let i = 1; i < deductions.length; i++) {
            const s = similarityScore(deductions[i], lastMove);
            if (s > bestScore) {
                best = deductions[i];
                bestScore = s;
            }
        }
        return best;
    }

    /**
     * Score how "similar" a candidate hint is to the player's last
     * move, additive across two independent dimensions:
     *
     *   Locality (+3)  — the deduction's natural region of reasoning
     *                    contains the player's last cell:
     *                      T-count: same row/col as the rule's line
     *                      T-three: same row/col as the rule's line
     *                      T-wall:  same connected wall component
     *                      L2/L3:   same row/col as the hypothesis
     *                      L4:      shares a row/col with hypothesis
     *
     *   Same rule (+2) — if the player followed a hint last move, we
     *                    know exactly which rule they just applied.
     *                    Prefer another hint of the same rule kind so
     *                    they can keep using the same mental model.
     *
     * A baseline of 0 is fine; ties resolve by row-major order, which
     * is good enough for a UI hint and avoids over-engineering this.
     */
    function similarityScore(deduction, lastMove) {
        const [lr, lc] = lastMove.cell;
        const r = deduction.reason;
        let score = 0;

        let localityMatched = false;
        if (r.kind === 'T-count') {
            if (r.orientation === 'row' && r.line === lr) localityMatched = true;
            else if (r.orientation === 'col' && r.line === lc) localityMatched = true;
        } else if (r.kind === 'T-three') {
            if (r.orientation === 'row' && deduction.cell[0] === lr) localityMatched = true;
            else if (r.orientation === 'col' && deduction.cell[1] === lc) localityMatched = true;
        } else if (r.kind === 'T-wall') {
            const wi = state.wallIndex;
            if (wi && typeof wi.wallComponentOf === 'function') {
                const a = wi.wallComponentOf(lr, lc);
                const b = wi.wallComponentOf(deduction.cell[0], deduction.cell[1]);
                if (a != null && a === b) localityMatched = true;
            }
        } else if (r.kind === 'L2' || r.kind === 'L3') {
            const hyp = r.hypothesis;
            if (hyp && hyp.cell) {
                const [hr, hc] = hyp.cell;
                if (r.orientation === 'row' && hr === lr) localityMatched = true;
                else if (r.orientation === 'col' && hc === lc) localityMatched = true;
            }
        } else if (r.kind === 'L4') {
            const hyp = r.hypothesis;
            if (hyp && hyp.cell) {
                const [hr, hc] = hyp.cell;
                if (hr === lr || hc === lc) localityMatched = true;
            }
        }
        if (localityMatched) score += 3;

        if (lastMove.reasonKind && lastMove.reasonKind === r.kind) score += 2;

        return score;
    }

    function renderHintBannerFromState() {
        const h = state.hint;
        if (!h || !state.hintBanner) return;
        const ui = uiTexts();
        let text = '';
        if (h.mode === 'error') {
            text = h.wrongCount === 1 ? ui.wrongOne : ui.wrongMany(h.wrongCount);
        } else if (h.mode === 'deduction' && h.reason) {
            const solver = window.PuzzleSolvers.tango;
            text = solver.describeReason(h.reason);
        } else if (h.mode === 'noHint') {
            text = h.filterTactic
                ? ui.noneFiltered(h.filterTactic, h.filterTactics.join('/'))
                : ui.noneAvail;
        }

        state.hintBanner.innerHTML = '';
        state.hintBanner.classList.toggle('error', h.mode === 'error');
        if (h.badgeText) {
            const badge = document.createElement('span');
            badge.className = 'hint-tier' + (h.mode === 'error' ? ' err' : '');
            badge.textContent = h.badgeText;
            state.hintBanner.appendChild(badge);
        }
        state.hintBanner.appendChild(document.createTextNode(text));
        state.hintBanner.hidden = false;
    }

    function clearHint() {
        if (!state.hint && state.hintBanner && state.hintBanner.hidden) return;
        const hadChain = !!(state.hint && state.hint.chainPlacements && state.hint.chainPlacements.length > 0);
        state.hint = null;
        if (state.hintBanner) {
            state.hintBanner.hidden = true;
            state.hintBanner.textContent = '';
            state.hintBanner.classList.remove('error');
        }
        applyHintHighlights();
        // Ghost glyphs live in the symbol layer (rebuilt by
        // repaintSymbols), so dropping them requires a repaint —
        // applyHintHighlights only touches the cell-background classes.
        if (hadChain && board) repaintSymbols();
    }

    /**
     * Toggle hint-target / hint-context / hint-violation CSS classes on
     * the existing cell-bg rects. `renderBoard` builds the rects in
     * row-major order so `cells[r * N + c]` gives the right node.
     *
     * Class priority (visual stacking):
     *   hint-target    — the cell the hint is about (pulsing yellow)
     *   hint-violation — cells where the rule actually breaks (red)
     *   hint-context   — supporting cells (soft yellow)
     */
    function applyHintHighlights() {
        if (!board) return;
        const N = state.puzzle ? state.puzzle.size : 0;
        const cellsGroup = board.querySelector('g.cells');
        if (!cellsGroup) return;
        const rects = cellsGroup.querySelectorAll('rect');
        for (const rect of rects) {
            rect.classList.remove('hint-target', 'hint-context', 'hint-violation');
        }
        if (!state.hint || N === 0) return;
        const taken = new Set();
        for (const [r, c] of state.hint.targetCells) {
            const i = r * N + c;
            taken.add(i);
            if (rects[i]) rects[i].classList.add('hint-target');
        }
        for (const [r, c] of (state.hint.violationCells || [])) {
            const i = r * N + c;
            if (taken.has(i)) continue;
            taken.add(i);
            if (rects[i]) rects[i].classList.add('hint-violation');
        }
        for (const [r, c] of (state.hint.contextCells || [])) {
            const i = r * N + c;
            if (taken.has(i)) continue;
            if (rects[i]) rects[i].classList.add('hint-context');
        }
    }

    function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = generatePuzzle(shell.size, shell.difficulty, seed);
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
            gameId: 'tango',
            difficulty: { default: 'medium' },
            size: { kind: 'segmented', default: 6 },
            onNewGame: startNewGame,
            onReset: resetPlacements,
            onReveal: repaintSymbols,
        });
        board = shell.dom.board;
        board.addEventListener('click', onBoardClick);

        state.hintBanner = document.getElementById('hint-banner');
        state.hintButton = document.getElementById('hint-btn');
        if (state.hintButton) {
            state.hintButton.addEventListener('click', showHint);
        }

        // Re-render the hint banner if the locale flips while a hint
        // is on screen (error / deduction / noHint all carry source
        // fields so the banner text can be regenerated in any mode).
        PC.i18n.subscribe(() => {
            if (state.hint) renderHintBannerFromState();
        });

        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
