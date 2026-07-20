/**
 * Sudoku — gameplay + SVG rendering.
 *
 * Puzzle generation lives in `js/generators/sudoku.js` and is exposed
 * via `window.PuzzleGenerators.sudoku(size, difficulty, seed)`. The
 * generator builds a full solution, then digs holes while a
 * technique-bounded solver confirms the puzzle stays uniquely solvable,
 * so every delivered board has a single solution reachable by the
 * difficulty's allowed techniques.
 *
 * Same architectural shape as queens.js / tango.js. Only depends on
 * window.PuzzleCommon (+ the generator above).
 *
 * Puzzle JSON contract:
 *   {
 *     id:         string,
 *     game:       'sudoku',
 *     size:       N,                 // 6 or 9
 *     difficulty: 'easy' | 'medium' | 'hard',
 *     boxRows:    int,               // height of a single box (2 for 6, 3 for 9)
 *     boxCols:    int,               // width of a single box  (3)
 *     prefilled:  int[N][N],         // 0 empty, 1..N for given digits (locked)
 *     solution:   int[N][N],         // always fully populated
 *     stats:      { clues, emptyCells, techniqueCounts }
 *   }
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const BOARD_SIZE = 480;
    const VIOLATION_DELAY_MS = 800;

    // -----------------------------------------------------------------
    // Puzzle generation (thin wrapper around the external generator).
    // -----------------------------------------------------------------

    function generatePuzzle(size, difficulty, seed) {
        return window.PuzzleGenerators.sudoku(size, difficulty, seed);
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        placements: null,   // int[N][N]; 0 = empty (only on non-prefilled cells)
        notes: null,        // Set<int>[N][N]; pencil marks (only on non-prefilled)
        selected: null,     // { r, c } | null
        notesMode: false,
        won: false,

        violations: null,         // bool[N][N], any-cell-in-any-conflict
        violationGroups: [],      // [{ kind, key, cells }] for partial refresh
        conflictPairs: 0,
        displayedViolations: null,
        displayedPairs: 0,
        violationTimer: null,

        hint: null,               // current hint descriptor, or null
        // The hint solver reads the player's notes as its candidate state
        // (empty-note cells fall back to basic candidates). A shown elimination
        // is pruned from the relevant cells' notes and stays pruned, so
        // reopening the hint continues to the next deduction.
        hintBanner: null,         // #hint-banner element
    };

    let shell = null;

    function emptyViolationGrid(N) {
        return Array.from({ length: N }, () => new Array(N).fill(false));
    }

    function emptyNotes(N) {
        return Array.from({ length: N }, () =>
            Array.from({ length: N }, () => new Set())
        );
    }

    function ensurePlacementsForCurrent() {
        const N = state.puzzle.size;
        state.placements = Array.from({ length: N }, () => new Array(N).fill(0));
        state.notes = emptyNotes(N);
        state.violations = emptyViolationGrid(N);
        state.violationGroups = [];
        state.conflictPairs = 0;
        state.displayedViolations = emptyViolationGrid(N);
        state.displayedPairs = 0;
        cancelViolationTimer();
        state.hint = null;
        state.won = false;
        // Keep current selection if it still fits the board; otherwise drop.
        if (state.selected && (state.selected.r >= N || state.selected.c >= N)) {
            state.selected = null;
        }
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

    /** Effective digit at a cell (prefilled clue if locked, else player). */
    function effective(r, c) {
        const p = state.puzzle.prefilled[r][c];
        return p !== 0 ? p : state.placements[r][c];
    }

    function isPrefilled(r, c) {
        return state.puzzle.prefilled[r][c] !== 0;
    }

    function boxIndexOf(r, c) {
        const { boxRows, boxCols, size } = state.puzzle;
        return Math.floor(r / boxRows) * Math.floor(size / boxCols)
             + Math.floor(c / boxCols);
    }

    // -----------------------------------------------------------------
    // Rules
    //
    // For every row / column / box we count digit occurrences. Any digit
    // with count > 1 marks every contributing cell as flagged and counts
    // as one "conflict" — the same metric Queens and Tango use, so the
    // status text stays consistent across games.
    // -----------------------------------------------------------------

    /**
     * Recompute violations from current placements. Two views are
     * produced: a cell-level `flagged` grid (used for the immediate
     * win-check + as the final "all conflicts" display after the
     * debounce), and a list of `groups` (used by the partial-refresh
     * logic so we can hide only the conflicts the latest toggle could
     * possibly have affected).
     */
    function recomputeViolations() {
        const N = state.puzzle.size;
        const flagged = emptyViolationGrid(N);
        const groups = [];

        // Build the constraint groups once, then scan each for duplicates.
        const rows = Array.from({ length: N }, () => []);
        const cols = Array.from({ length: N }, () => []);
        const boxes = Array.from({ length: N }, () => []);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                rows[r].push([r, c]);
                cols[c].push([r, c]);
                boxes[boxIndexOf(r, c)].push([r, c]);
            }
        }

        function scan(kind, key, cells) {
            const buckets = new Map();
            for (const [r, c] of cells) {
                const v = effective(r, c);
                if (v === 0) continue;
                if (!buckets.has(v)) buckets.set(v, []);
                buckets.get(v).push([r, c]);
            }
            for (const dupCells of buckets.values()) {
                if (dupCells.length > 1) {
                    for (const [r, c] of dupCells) flagged[r][c] = true;
                    groups.push({ kind, key, cells: dupCells });
                }
            }
        }

        for (let r = 0; r < N; r++) scan('row', r, rows[r]);
        for (let c = 0; c < N; c++) scan('col', c, cols[c]);
        for (let b = 0; b < N; b++) scan('box', b, boxes[b]);

        state.violations = flagged;
        state.violationGroups = groups;
        state.conflictPairs = groups.length;
    }

    /**
     * Is the given conflict group "owned" by a toggle at (r0, c0)? A
     * group is owned when toggling that cell could change the group:
     * row R groups are owned by anything in row R, col C by anything
     * in col C, box B by anything in that box. Owned groups get hidden
     * for VIOLATION_DELAY_MS so the player isn't pestered as they edit.
     * Unowned groups stay visible because they cannot possibly have
     * changed.
     */
    function isGroupOwnedBy(group, r0, c0) {
        if (group.kind === 'row') return group.key === r0;
        if (group.kind === 'col') return group.key === c0;
        if (group.kind === 'box') return group.key === boxIndexOf(r0, c0);
        return false;
    }

    function isFullyFilled() {
        const N = state.puzzle.size;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (effective(r, c) === 0) return false;
            }
        }
        return true;
    }

    /**
     * Win check assumes `recomputeViolations` has already been called for
     * the current placements; callers are responsible for that. Keeping
     * win logic separate lets us reuse the recompute step for the
     * violation-display debounce without paying for it twice.
     */
    function checkWin() {
        return isFullyFilled() && state.conflictPairs === 0;
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    // Sudoku-specific DOM. The shell owns the toolbar / status row.
    let board = null;
    let keypad = null;
    let notesBtn = null; // populated by buildKeypad

    function cellRect(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { x: c * cs, y: r * cs, size: cs };
    }

    function renderBoard() {
        const N = state.puzzle.size;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        const cs = BOARD_SIZE / N;
        const { boxRows, boxCols } = state.puzzle;

        const W = N * cs;

        // Layer: cell backgrounds (white; prefilled get a darker tint).
        // Drawn strokeless — all grid lines live in the `grid` layer
        // below, which sits ABOVE the focus ring so the ring reads as
        // tucked under the native grid.
        const bgGroup = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const cls = 'cell-bg' + (isPrefilled(r, c) ? ' prefilled' : '');
                bgGroup.appendChild(PC.svgEl('rect', {
                    class: cls,
                    x, y, width: size, height: size,
                    fill: isPrefilled(r, c) ? '#e6e8ee' : '#ffffff',
                    style: 'stroke: none',
                }));
            }
        }
        svg.appendChild(bgGroup);

        // Layer: selection backdrop (peer / same-digit tints).
        const selectGroup = PC.svgEl('g', { class: 'select' });
        selectGroup.setAttribute('id', 'select');
        svg.appendChild(selectGroup);

        // Layer: below-symbol hint tint (error red wash).
        const hintGroup = PC.svgEl('g', { class: 'hint' });
        hintGroup.setAttribute('id', 'hint');
        svg.appendChild(hintGroup);

        // Layer: focus ring — below the grid so the native grid lines are
        // drawn on top of it (the ring tucks under the grid, its outer
        // edge sitting on the cell boundary).
        const ringGroup = PC.svgEl('g', { class: 'select-ring' });
        ringGroup.setAttribute('id', 'select-ring');
        svg.appendChild(ringGroup);

        // Layer: grid lines — thin cell separators + thick box borders +
        // outer frame, all above the ring so it never hides the grid.
        const gridGroup = PC.svgEl('g', { class: 'grid' });
        for (let i = 0; i <= N; i++) {
            const hThick = i % boxRows === 0;
            gridGroup.appendChild(PC.svgEl('line', {
                class: hThick ? 'region-border' : 'grid-line',
                x1: 0, y1: i * cs, x2: W, y2: i * cs,
            }));
            const vThick = i % boxCols === 0;
            gridGroup.appendChild(PC.svgEl('line', {
                class: vThick ? 'region-border' : 'grid-line',
                x1: i * cs, y1: 0, x2: i * cs, y2: W,
            }));
        }
        svg.appendChild(gridGroup);

        // Layer: symbols + notes + violations + reveal hint.
        const symbolGroup = PC.svgEl('g', { class: 'symbols' });
        symbolGroup.setAttribute('id', 'symbols');
        svg.appendChild(symbolGroup);

        // Layer: hint dim + hint candidates. Above the symbols so it can
        // fade the digits of non-spotlit cells (the "dim everything else"
        // effect) and draw computed candidate marks on the lit cells for
        // advanced-technique hints. Below the hit layer so clicks work.
        const dimGroup = PC.svgEl('g', { class: 'hint-dim' });
        dimGroup.setAttribute('id', 'hint-dim');
        svg.appendChild(dimGroup);

        // Layer: invisible click targets (last, so they sit on top). All
        // cells get a hit rect, even prefilled ones — clicking them is
        // still useful for selection / focus traversal.
        const hitGroup = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                hitGroup.appendChild(PC.svgEl('rect', {
                    class: 'cell-hover',
                    x, y, width: size, height: size,
                    'data-r': r,
                    'data-c': c,
                }));
            }
        }
        svg.appendChild(hitGroup);

        repaintSelection();
        repaintHint();
        repaintSymbols();
    }

    /** Redraw only the selection-tint layer. Cheap and called on every
     *  selection change / arrow-key navigation. */
    function repaintSelection() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const group = board.querySelector('#select');
        const ringGroup = board.querySelector('#select-ring');
        if (!group || !ringGroup) return;
        while (group.firstChild) group.removeChild(group.firstChild);
        while (ringGroup.firstChild) ringGroup.removeChild(ringGroup.firstChild);

        const sel = state.selected;
        if (!sel) return;

        const selDigit = effective(sel.r, sel.c);
        const selBox = boxIndexOf(sel.r, sel.c);
        // While a hint is on screen the dim-spotlight is the dominant
        // signal, so we drop the row/col/box + same-digit tints and keep
        // only the focus ring (which marks the hint's target cell).
        const hintActive = !!state.hint;

        // Focus ring — drawn as four independent edges so each side can be
        // nudged inward by exactly the neighbouring native line's
        // thickness. That keeps the ring a uniform, fully-visible weight on
        // all four sides (a thick box border no longer eats into it) while
        // it still hugs the inside of the cell. Green normally, black on a
        // pre-filled (given) cell.
        const rw = 3; // must match .cell-ring stroke-width
        const { boxRows, boxCols } = state.puzzle;
        // Inset for a side = half the native line's width there + half the
        // ring's width, so the ring sits just inside that native line.
        const inset = (thick) => (thick ? 1.5 : 0.5) + rw / 2;
        const iT = inset(sel.r % boxRows === 0);
        const iB = inset((sel.r + 1) % boxRows === 0);
        const iL = inset(sel.c % boxCols === 0);
        const iR = inset((sel.c + 1) % boxCols === 0);
        const x0 = sel.c * cs;
        const y0 = sel.r * cs;
        const x1 = (sel.c + 1) * cs;
        const y1 = (sel.r + 1) * cs;
        const ringCls = 'cell-ring' + (isPrefilled(sel.r, sel.c) ? ' given' : '');
        const edge = (ax, ay, bx, by) => ringGroup.appendChild(PC.svgEl('line', {
            class: ringCls, x1: ax, y1: ay, x2: bx, y2: by,
        }));
        edge(x0 + iL, y0 + iT, x1 - iR, y0 + iT); // top
        edge(x0 + iL, y1 - iB, x1 - iR, y1 - iB); // bottom
        edge(x0 + iL, y0 + iT, x0 + iL, y1 - iB); // left
        edge(x1 - iR, y0 + iT, x1 - iR, y1 - iB); // right

        if (hintActive) return;

        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (r === sel.r && c === sel.c) continue;
                const isPeer = (r === sel.r || c === sel.c
                    || boxIndexOf(r, c) === selBox);
                const isSameDigit = selDigit !== 0 && effective(r, c) === selDigit;
                let cls = null;
                if (isSameDigit) cls = 'cell-select same';
                else if (isPeer) cls = 'cell-select peer';
                if (!cls) continue;
                group.appendChild(PC.svgEl('rect', {
                    class: cls,
                    x: c * cs, y: r * cs, width: cs, height: cs,
                }));
            }
        }
    }

    // Centre of the pencil-mark slot for digit `d` inside cell (r,c). Slots
    // are spread with equal gaps that INCLUDE the cell border (…/(box+1)),
    // so the margin to the cell edge matches the gap between digits instead
    // of being half of it. Shared by notes, the reveal hint and hint marks.
    function noteSlot(r, c, d, cs, boxRows, boxCols) {
        const nr = Math.floor((d - 1) / boxCols);
        const nc = (d - 1) % boxCols;
        return {
            x: c * cs + (cs * (nc + 1)) / (boxCols + 1),
            y: r * cs + (cs * (nr + 1)) / (boxRows + 1),
        };
    }

    function repaintSymbols() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const { boxRows, boxCols } = state.puzzle;
        const group = board.querySelector('#symbols');
        while (group.firstChild) group.removeChild(group.firstChild);

        const digitFont = Math.max(20, Math.floor(cs * 0.62));
        const noteFont = Math.max(9, Math.floor(cs * 0.22));

        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = effective(r, c);
                if (v !== 0) {
                    const lockedClass = isPrefilled(r, c) ? ' prefilled' : '';
                    const text = PC.svgEl('text', {
                        class: `symbol digit${lockedClass}`,
                        x: c * cs + cs / 2,
                        y: r * cs + cs / 2,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        // Digits 0-9 are visually centred lower than the
                        // dominant-baseline=middle mark in most fonts;
                        // they need a larger dy than the top-heavy
                        // glyphs (♛, ☀, ☾) used by Queens/Tango.
                        dy: '0.12em',
                        'font-size': digitFont,
                    });
                    text.textContent = String(v);
                    group.appendChild(text);
                } else {
                    // While the solution is revealed we hide the player's
                    // notes so the small answer digit never collides with a
                    // pencil mark (they share the same slots).
                    if (shell.revealed) continue;
                    // Notes: lay them out in a sub-grid matching the box
                    // shape (so 9×9 → 3×3, 6×6 → 2×3 with digits 1–6).
                    const notes = state.notes[r][c];
                    if (notes.size === 0) continue;
                    for (const d of notes) {
                        const { x: nx, y: ny } = noteSlot(r, c, d, cs, boxRows, boxCols);
                        const text = PC.svgEl('text', {
                            class: 'symbol note',
                            x: nx, y: ny,
                            'text-anchor': 'middle',
                            'dominant-baseline': 'middle',
                            dy: '0.12em',
                            'font-size': noteFont,
                        });
                        text.textContent = String(d);
                        group.appendChild(text);
                    }
                }
            }
        }

        // Violations (debounced)
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

        // Reveal: tiny solution digit in the top-left note slot of every
        // player-editable cell (prefilled cells already show the answer).
        // Player notes are hidden while revealed, so this never overlaps.
        if (shell.revealed && state.puzzle && state.puzzle.solution) {
            const sol = state.puzzle.solution;
            const hintFont = Math.max(9, Math.floor(cs * 0.22));
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (isPrefilled(r, c)) continue;
                    const slot = noteSlot(r, c, 1, cs, boxRows, boxCols);
                    const text = PC.svgEl('text', {
                        class: 'symbol reveal-hint',
                        x: slot.x,
                        y: slot.y,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.12em',
                        'font-size': hintFont,
                    });
                    text.textContent = String(sol[r][c]);
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
    // Hint
    //
    // Surfaces what the tactic-bounded solver would do next, so the
    // player can see the reasoning. Priority:
    //   1. If the player has a wrong digit (differs from the unique
    //      solution): flag it. If it forms an actual duplicate we name
    //      the offending unit ("too many Xs"); otherwise a generic
    //      "this cell is incorrect".
    //   2. Otherwise the next forced deduction (fullHouse → naked
    //      single → hidden single), highlighting the target cell and
    //      the unit / peers the deduction reads from.
    // -----------------------------------------------------------------

    function unitName(kind) {
        if (kind === 'row') return PC.i18n.t('sudokuHintUnitRow');
        if (kind === 'col') return PC.i18n.t('sudokuHintUnitCol');
        return PC.i18n.t('sudokuHintUnitBox');
    }

    /** Cells belonging to a given unit (row/col/box index). */
    function unitCells(kind, index) {
        const N = state.puzzle.size;
        const out = [];
        if (kind === 'row') {
            for (let c = 0; c < N; c++) out.push([index, c]);
        } else if (kind === 'col') {
            for (let r = 0; r < N; r++) out.push([r, index]);
        } else {
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (boxIndexOf(r, c) === index) out.push([r, c]);
                }
            }
        }
        return out;
    }

    function effectiveGrid() {
        const N = state.puzzle.size;
        const grid = [];
        for (let r = 0; r < N; r++) {
            const row = [];
            for (let c = 0; c < N; c++) row.push(effective(r, c));
            grid.push(row);
        }
        return grid;
    }

    function sudokuSolver() {
        return (window.PuzzleSolvers && window.PuzzleSolvers.sudoku) || null;
    }

    // A rule-violation hint (wrong entry / contradiction), or null. Takes
    // priority over any deduction and is terminal (no walkthrough).
    function errorHint(S) {
        const N = state.puzzle.size;
        const { boxRows, boxCols, solution } = state.puzzle;
        const grid = effectiveGrid();
        const wrong = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (isPrefilled(r, c)) continue;
                const v = state.placements[r][c];
                if (v !== 0 && v !== solution[r][c]) wrong.push([r, c]);
            }
        }
        if (!wrong.length) return null;
        const contra = S.findContradiction(grid, N, boxRows, boxCols);
        if (contra) {
            return {
                kind: 'error', variant: 'contradiction',
                cells: contra.cells, unitKind: contra.unitKind, value: contra.value,
            };
        }
        return { kind: 'error', variant: 'wrong', cells: wrong };
    }

    // Pencil marks that are impossible given the placed digits (the same digit
    // sits in the cell's row, column or box). Returned as a conflict hint so we
    // can flag + clear them before any deduction — mirroring the conflict-first
    // rule for placed digits.
    function conflictNotesHint(S) {
        const N = state.puzzle.size;
        const { boxRows, boxCols } = state.puzzle;
        const basicState = S.makeState(effectiveGrid(), N, boxRows, boxCols);
        const elims = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (isPrefilled(r, c) || effective(r, c) !== 0) continue;
                const basic = basicState.cands[r][c];
                for (const d of state.notes[r][c]) {
                    if (!(basic & (1 << (d - 1)))) elims.push({ r, c, d });
                }
            }
        }
        if (!elims.length) return null;
        return { kind: 'noteConflict', eliminations: elims };
    }

    // Cells where the player has pencil marks but has crossed out the one that
    // is actually correct — a self-inflicted dead end the note-based solver
    // would otherwise follow astray. Returned so we can add the digit back.
    function missingSolutionNoteHint() {
        const N = state.puzzle.size;
        const { solution } = state.puzzle;
        const restores = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (isPrefilled(r, c) || effective(r, c) !== 0) continue;
                const notes = state.notes[r][c];
                if (notes.size === 0) continue; // empty = every digit still open
                if (!notes.has(solution[r][c])) {
                    restores.push({ r, c, d: solution[r][c] });
                }
            }
        }
        if (!restores.length) return null;
        return { kind: 'noteMissing', restores };
    }

    // Build the solver the hint reasons on. Its candidates ARE the player's
    // notes (intersected with the basic candidates so a stray/typo pencil mark
    // can never make the solver place an impossible digit); cells the player
    // hasn't noted yet fall back to their basic candidates. Also returns the
    // raw `basic` grid so we can fill in only the cells a step touches.
    function buildHintSolver(S) {
        const N = state.puzzle.size;
        const { boxRows, boxCols } = state.puzzle;
        const st = S.makeState(effectiveGrid(), N, boxRows, boxCols);
        const basic = st.cands.map((row) => row.slice());
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (isPrefilled(r, c) || effective(r, c) !== 0) continue;
                let m = 0;
                for (const d of state.notes[r][c]) m |= 1 << (d - 1);
                st.cands[r][c] = m ? (m & basic[r][c]) : basic[r][c];
            }
        }
        return { st, basic };
    }

    // Pencil in the true candidates for only the cells a step reasons about
    // (its pattern + elimination cells) — and only where the player has no
    // notes yet, so cells already pruned by earlier steps are never re-filled.
    function fillStepNotes(step, basic) {
        const cells = step.cells.concat(step.eliminations.map((e) => [e.r, e.c]));
        for (const [r, c] of cells) {
            if (isPrefilled(r, c) || effective(r, c) !== 0) continue;
            if (state.notes[r][c].size > 0) continue; // keep pruned cells intact
            const set = state.notes[r][c];
            for (const d of bitsOfMask(basic[r][c])) set.add(d);
        }
    }

    // Digits present in a candidate bitmask.
    function bitsOfMask(mask) {
        const out = [];
        let d = 1;
        while (mask) { if (mask & 1) out.push(d); mask >>>= 1; d += 1; }
        return out;
    }

    // Row + column + box peers of a cell.
    function peerCells(r0, c0) {
        const N = state.puzzle.size;
        const box0 = boxIndexOf(r0, c0);
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (r === r0 && c === c0) continue;
                if (r === r0 || c === c0 || boxIndexOf(r, c) === box0) out.push([r, c]);
            }
        }
        return out;
    }

    // For a hidden single (digit d forced into (tr,tc) of a unit): the placed
    // copies of d elsewhere that block d from the unit's OTHER empty cells —
    // i.e. the "because of these other d's" cells the hint text names.
    function hiddenSingleBlockers(unitKind, unitIndex, d, tr, tc) {
        const out = [];
        const seen = new Set();
        const N = state.puzzle.size;
        for (const [r, c] of unitCells(unitKind, unitIndex)) {
            if (r === tr && c === tc) continue;
            if (effective(r, c) !== 0) continue;
            for (const [pr, pc] of peerCells(r, c)) {
                if (effective(pr, pc) === d) {
                    const k = pr * N + pc;
                    if (!seen.has(k)) { seen.add(k); out.push([pr, pc]); }
                }
            }
        }
        return out;
    }

    // The cell a hint wants the player to look at (target of a step, or
    // the first offending cell of an error) — used to move the cursor
    // there so the player can act on the hint immediately.
    function hintFocusCell(h) {
        if (!h) return null;
        if (h.kind === 'error' && h.cells && h.cells.length) return h.cells[0];
        if (h.kind === 'step') {
            const s = h.step;
            if (s.placements.length) return [s.placements[0].r, s.placements[0].c];
            if (s.cells && s.cells.length) return s.cells[0];
            if (s.eliminations.length) {
                return [s.eliminations[0].r, s.eliminations[0].c];
            }
        }
        return null;
    }

    // Is the current hint a pure-elimination step (i.e. the walkthrough can
    // advance past it on the next press)?
    function hintIsElimination(h) {
        return !!(h && h.kind === 'step' && h.step
            && h.step.placements.length === 0
            && h.step.eliminations.length);
    }

    function setHint(h) {
        state.hint = h;
        // Move the cursor onto the actionable cell for placements / errors so
        // the player can act right away; elimination steps have no single
        // "target", so we leave the cursor where it is to avoid jumpiness.
        if (h && (h.kind === 'error'
            || (h.kind === 'step' && h.step && h.step.placements.length))) {
            const focus = hintFocusCell(h);
            if (focus) selectCell(focus[0], focus[1]);
        }
        // The walkthrough edits the note layer, so refresh it too.
        repaintSymbols();
        renderHintBanner();
        repaintHint();
    }

    function showHint() {
        if (!state.puzzle || state.won) return;
        const S = sudokuSolver();
        if (!S) return;

        // Toggle: a shown hint is dismissed on the next press. The candidate
        // removals it made stay in the notes, so reopening continues onward.
        if (state.hint) { clearHint(); return; }

        // Rule violations win over any deduction.
        const err = errorHint(S);
        if (err) { setHint(err); return; }

        // Then: pencil marks that conflict with a placed digit. Flag + clear
        // them (red strike) before deducing, so the notes the deduction reads
        // always match what's shown.
        const noteConflict = conflictNotesHint(S);
        if (noteConflict) {
            for (const e of noteConflict.eliminations) {
                state.notes[e.r][e.c].delete(e.d);
            }
            setHint(noteConflict);
            return;
        }

        // Then: a cell where the correct candidate has been crossed out. Add it
        // back (green) so the note-based deduction can't be led astray.
        const noteMissing = missingSolutionNoteHint();
        if (noteMissing) {
            for (const e of noteMissing.restores) state.notes[e.r][e.c].add(e.d);
            setHint(noteMissing);
            return;
        }

        const techniques = S.TECHNIQUES_BY_DIFFICULTY[state.puzzle.difficulty];
        const { st, basic } = buildHintSolver(S);
        const step = S.nextStep(st, techniques);
        if (!step) { setHint({ kind: 'none' }); return; }

        // Showing an elimination commits it: pencil in the candidates for just
        // the cells it touches (leaving already-pruned cells alone), then strike
        // the removed candidate and drop it from the notes for good — never
        // re-added — so reopening the hint continues where this one left off.
        // Singles never touch the notes.
        if (step.eliminations.length) {
            fillStepNotes(step, basic);
            for (const e of step.eliminations) state.notes[e.r][e.c].delete(e.d);
        }
        setHint({ kind: 'step', step });
    }

    function clearHint() {
        state.hint = null;
        // The auto-filled / pruned candidate notes are kept — dropping only
        // the overlay is what makes "dismiss, reopen, continue" work.
        renderHintBanner();
        repaintHint();
        repaintSymbols();
        // Selection tints (peer / same-digit) are suppressed while a hint
        // is up, so restore them now that it's gone.
        repaintSelection();
    }

    /**
     * Redraw the hint layers.
     *   #hint      (below the symbols) — soft cell tints: the unit/pattern
     *              cells the current step reasons about, plus a green wash on
     *              a placement target. Sits under the notes so they read.
     *   #hint-dim  (above the symbols) — red strike-through over the exact
     *              candidate(s) this step removes (the notes already show the
     *              full, accumulating candidate view via repaintSymbols).
     * Errors keep the old red-wash + dim-everything-else spotlight.
     */
    function repaintHint() {
        const belowGroup = board && board.querySelector('#hint');
        const dimGroup = board && board.querySelector('#hint-dim');
        if (!belowGroup || !dimGroup) return;
        while (belowGroup.firstChild) belowGroup.removeChild(belowGroup.firstChild);
        while (dimGroup.firstChild) dimGroup.removeChild(dimGroup.firstChild);
        const h = state.hint;
        if (!h || h.kind === 'none') return;

        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const { boxRows, boxCols } = state.puzzle;
        const tint = (r, c, fill, op) => belowGroup.appendChild(PC.svgEl('rect', {
            x: c * cs, y: r * cs, width: cs, height: cs,
            fill, 'fill-opacity': op,
        }));
        const noteFont = Math.max(9, Math.floor(cs * 0.22));
        // A coloured copy of a candidate drawn above the notes: red + struck
        // for a removal, green for one added back.
        const drawCand = (r, c, d, color, struck) => {
            const { x, y } = noteSlot(r, c, d, cs, boxRows, boxCols);
            const txt = PC.svgEl('text', {
                x, y, 'text-anchor': 'middle', 'dominant-baseline': 'middle',
                dy: '0.12em', 'font-size': noteFont,
                fill: color, 'font-weight': 700,
            });
            if (struck) txt.setAttribute('text-decoration', 'line-through');
            txt.textContent = String(d);
            dimGroup.appendChild(txt);
        };
        const strike = (r, c, d) => drawCand(r, c, d, '#ef5350', true);
        const dimExcept = (litSet) => {
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (litSet.has(r * N + c)) continue;
                    dimGroup.appendChild(PC.svgEl('rect', {
                        class: 'hint-dim-cell', x: c * cs, y: r * cs,
                        width: cs, height: cs,
                    }));
                }
            }
        };

        if (h.kind === 'error') {
            const errSet = new Set(h.cells.map(([r, c]) => r * N + c));
            for (const [r, c] of h.cells) tint(r, c, '#ef5350', 0.35);
            dimExcept(errSet);
            return;
        }

        if (h.kind === 'noteConflict') {
            const lit = new Set(h.eliminations.map((e) => e.r * N + e.c));
            const seen = new Set();
            for (const e of h.eliminations) {
                const k = e.r * N + e.c;
                if (!seen.has(k)) { seen.add(k); tint(e.r, e.c, '#ef5350', 0.10); }
            }
            dimExcept(lit);
            for (const e of h.eliminations) strike(e.r, e.c, e.d);
            return;
        }

        if (h.kind === 'noteMissing') {
            const lit = new Set(h.restores.map((e) => e.r * N + e.c));
            const seen = new Set();
            for (const e of h.restores) {
                const k = e.r * N + e.c;
                if (!seen.has(k)) { seen.add(k); tint(e.r, e.c, '#2e7d32', 0.14); }
            }
            dimExcept(lit);
            for (const e of h.restores) drawCand(e.r, e.c, e.d, '#2e7d32', false);
            return;
        }

        const s = h.step;
        const target = s.placements.length ? s.placements[0] : null;
        const targetKey = target ? target.r * N + target.c : -1;

        // Cells the spotlight keeps bright: the unit, the pattern cells, the
        // target, and any cell losing a candidate. Everything else is dimmed.
        const lit = new Set();
        if (s.unit) {
            for (const [r, c] of unitCells(s.unit.kind, s.unit.index)) {
                lit.add(r * N + c);
            }
        }
        for (const [r, c] of s.cells) lit.add(r * N + c);
        for (const e of s.eliminations) lit.add(e.r * N + e.c);
        if (target) lit.add(targetKey);
        // Naked single: light the row/col/box peers — they're the "根據其所屬
        // 行、列、區域" that forces the single.
        if (target && s.technique === 'nakedSingle') {
            for (const [r, c] of peerCells(target.r, target.c)) lit.add(r * N + c);
        }
        // Hidden single: keep the blocking copies of the digit bright too —
        // they're the whole reason the digit is forced into the target.
        let blockers = [];
        if (target && s.technique === 'hiddenSingle' && s.unit) {
            blockers = hiddenSingleBlockers(
                s.unit.kind, s.unit.index, target.value, target.r, target.c);
            for (const [r, c] of blockers) lit.add(r * N + c);
        }

        // Tints under the notes: stronger wash on the pattern cells (the
        // "reason"), green on a placement target, faint red on cells losing a
        // candidate (so they read even outside the unit, e.g. X-Wing).
        for (const [r, c] of s.cells) {
            if (r * N + c !== targetKey) tint(r, c, '#2196f3', 0.18);
        }
        for (const [r, c] of blockers) tint(r, c, '#2196f3', 0.18);
        const elimCellSeen = new Set();
        for (const e of s.eliminations) {
            const k = e.r * N + e.c;
            if (elimCellSeen.has(k)) continue;
            elimCellSeen.add(k);
            tint(e.r, e.c, '#ef5350', 0.10);
        }
        if (target) tint(target.r, target.c, '#2e7d32', 0.22);

        // Dim everything the step doesn't touch (above the symbols, so notes
        // fade too), restoring the focused spotlight.
        dimExcept(lit);

        // Red strike over each candidate this step removes. It's already gone
        // from the note layer, so draw a red, struck copy to show what went.
        for (const e of s.eliminations) strike(e.r, e.c, e.d);
    }

    function renderHintBanner() {
        const el = state.hintBanner;
        if (!el) return;
        const h = state.hint;
        if (!h) { el.hidden = true; el.innerHTML = ''; el.classList.remove('error'); return; }

        const t = (key, ...args) => PC.i18n.t(key, ...args);
        let isError = false;
        let text = '';

        if (h.kind === 'error') {
            isError = true;
            if (h.variant === 'contradiction') {
                text = t('sudokuHintContradiction',
                    unitName(h.unitKind), h.value, state.puzzle.size);
            } else {
                text = t('sudokuHintWrong');
            }
        } else if (h.kind === 'noteConflict') {
            isError = true;
            text = t('sudokuHintNoteConflict');
        } else if (h.kind === 'noteMissing') {
            text = t('sudokuHintNoteMissing');
        } else if (h.kind === 'step') {
            const s = h.step;
            const u = s.unit ? unitName(s.unit.kind) : '';
            const dstr = s.digits.join('、');
            switch (s.technique) {
                case 'fullHouse':
                    text = t('sudokuHintFullHouse', u, s.digits[0]); break;
                case 'nakedSingle':
                    text = t('sudokuHintNaked', s.digits[0]); break;
                case 'hiddenSingle':
                    text = t('sudokuHintHidden', u, s.digits[0]); break;
                case 'lockedPointing':
                    text = t('sudokuHintLockedPointing', u, dstr); break;
                case 'lockedClaiming':
                    text = t('sudokuHintLockedClaiming', u, dstr); break;
                case 'nakedPair':
                    text = t('sudokuHintNakedPair', u, dstr); break;
                case 'hiddenPair':
                    text = t('sudokuHintHiddenPair', u, dstr); break;
                case 'nakedTriple':
                    text = t('sudokuHintNakedTriple', u, dstr); break;
                case 'hiddenTriple':
                    text = t('sudokuHintHiddenTriple', u, dstr); break;
                case 'xWing':
                    text = t('sudokuHintXWing', dstr); break;
                case 'xyWing':
                    text = t('sudokuHintXYWing', dstr); break;
                default:
                    text = t('sudokuHintNoAvail');
            }
        } else {
            text = t('sudokuHintNoAvail');
        }

        // Elimination steps don't change the board, so signal that pressing
        // Hint again walks to the next deduction.
        if (hintIsElimination(h)) text += t('sudokuHintContinue');

        // No tier badge — Queens/Tango don't show one either; the red
        // banner styling alone signals an error.
        el.classList.toggle('error', isError);
        el.textContent = text;
        el.hidden = false;
    }

    // -----------------------------------------------------------------
    // Keypad
    // -----------------------------------------------------------------

    function buildKeypad() {
        const N = state.puzzle.size;
        const { boxCols } = state.puzzle;

        // The digit pad mirrors the puzzle's box shape: digits 1..N are
        // laid out in a (N/boxCols) × boxCols grid, so the position of
        // each key matches the position of that digit inside one Sudoku
        // box (e.g. 9×9 → familiar 3×3 phone-pad; 6×6 → 2×3). Mode
        // controls (Notes / Erase) live in a separate row underneath.
        keypad.style.setProperty('--keypad-box-cols', String(boxCols));
        while (keypad.firstChild) keypad.removeChild(keypad.firstChild);

        const digits = PC.el('div', { class: 'keypad-digits' });
        for (let d = 1; d <= N; d++) {
            const btn = PC.el('button', {
                type: 'button',
                class: 'keypad-btn',
                'data-digit': String(d),
                'aria-label': `Digit ${d}`,
            }, String(d));
            btn.addEventListener('click', () => onKeypadDigit(d));
            digits.appendChild(btn);
        }
        keypad.appendChild(digits);

        const actions = PC.el('div', { class: 'keypad-actions' });
        // Icon + label as separate children: the label span carries
        // data-i18n so translateNode can re-localise it on a language
        // flip without wiping the injected SVG icon.
        notesBtn = PC.el('button', {
            type: 'button',
            class: 'keypad-btn notes-toggle',
            'aria-pressed': 'false',
            'aria-label': 'Toggle pencil-mark notes mode',
            title: 'Toggle pencil-mark notes (N)',
        }, PC.icon('pencil'),
            PC.el('span', { 'data-i18n': 'sudokuNotes' }, PC.i18n.t('sudokuNotes')));
        notesBtn.addEventListener('click', toggleNotesMode);
        actions.appendChild(notesBtn);

        const eraseBtn = PC.el('button', {
            type: 'button',
            class: 'keypad-btn erase',
            'aria-label': 'Erase',
            'data-i18n-aria-label': 'sudokuEraseAria',
            'data-i18n-title': 'sudokuEraseTitle',
            title: PC.i18n.t('sudokuEraseTitle'),
        }, PC.icon('eraser'),
            PC.el('span', { 'data-i18n': 'sudokuErase' }, PC.i18n.t('sudokuErase')));
        eraseBtn.addEventListener('click', eraseSelected);
        actions.appendChild(eraseBtn);

        keypad.appendChild(actions);

        updateKeypadMode();
    }

    function updateKeypadMode() {
        keypad.classList.toggle('notes-mode', state.notesMode);
        if (notesBtn) {
            notesBtn.classList.toggle('active', state.notesMode);
            notesBtn.setAttribute('aria-pressed', state.notesMode ? 'true' : 'false');
        }
    }

    // -----------------------------------------------------------------
    // Event handlers
    // -----------------------------------------------------------------

    function selectCell(r, c) {
        if (!state.puzzle) return;
        const N = state.puzzle.size;
        if (r < 0 || r >= N || c < 0 || c >= N) return;
        state.selected = { r, c };
        repaintSelection();
    }

    function moveSelection(dr, dc) {
        if (!state.puzzle) return;
        // While a hint is on screen the selection is locked to the hint's cell.
        if (state.hint) return;
        const N = state.puzzle.size;
        if (!state.selected) {
            selectCell(0, 0);
            return;
        }
        const nr = PC.clamp(state.selected.r + dr, 0, N - 1);
        const nc = PC.clamp(state.selected.c + dc, 0, N - 1);
        selectCell(nr, nc);
    }

    /**
     * Recompute the displayed-violation overlay after a toggle at
     * (r0, c0). Conflicts whose constraint group is NOT owned by the
     * toggle show up immediately — they cannot have changed, so there's
     * no reason to make the player wait. Conflicts owned by the toggle
     * are hidden, and the full set is flushed via commitViolationDisplay
     * after VIOLATION_DELAY_MS so the player isn't pestered mid-edit.
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

    function fillDigit(d) {
        if (!state.puzzle || state.won) return;
        const sel = state.selected;
        if (!sel) return;
        if (isPrefilled(sel.r, sel.c)) return;
        const cur = state.placements[sel.r][sel.c];
        if (cur === d) {
            // Same key again clears the cell.
            state.placements[sel.r][sel.c] = 0;
        } else {
            state.placements[sel.r][sel.c] = d;
            state.notes[sel.r][sel.c].clear();
        }
        afterPlacementChange(sel.r, sel.c);
    }

    function toggleNote(d) {
        if (!state.puzzle || state.won) return;
        const sel = state.selected;
        if (!sel) return;
        if (isPrefilled(sel.r, sel.c)) return;
        // Notes only show on cells without a final digit. Adding a note
        // to a digit-occupied cell would visually clobber the digit, so
        // we drop the digit first. Dropping it can resolve a conflict,
        // so we go through the standard recompute path.
        const hadDigit = state.placements[sel.r][sel.c] !== 0;
        if (hadDigit) state.placements[sel.r][sel.c] = 0;
        const set = state.notes[sel.r][sel.c];
        if (set.has(d)) set.delete(d); else set.add(d);
        if (hadDigit) {
            afterPlacementChange(sel.r, sel.c);
        } else {
            // Notes don't participate in violation checks, so we can skip
            // the recompute entirely and just repaint the symbol layer.
            clearHint();
            repaintSymbols();
        }
    }

    function onKeypadDigit(d) {
        if (state.notesMode) toggleNote(d);
        else fillDigit(d);
    }

    function eraseSelected() {
        if (!state.puzzle || state.won) return;
        const sel = state.selected;
        if (!sel) return;
        if (isPrefilled(sel.r, sel.c)) return;
        state.placements[sel.r][sel.c] = 0;
        state.notes[sel.r][sel.c].clear();
        afterPlacementChange(sel.r, sel.c);
    }

    /**
     * Shared "after the player edited a cell" tail: re-check rules, then
     * either fire the win path or refresh the violation overlay. The
     * (r, c) coordinates of the edit are forwarded so the partial-refresh
     * logic knows which conflict groups to debounce.
     */
    function afterPlacementChange(r, c) {
        // Any edit invalidates the shown hint (the board it described
        // has changed), so drop it before recomputing.
        clearHint();
        recomputeViolations();
        if (checkWin() && !state.won) {
            state.won = true;
            cancelViolationTimer();
            state.displayedViolations = emptyViolationGrid(state.puzzle.size);
            state.displayedPairs = 0;
            shell.markSolved();
            repaintSelection();
            repaintSymbols();
            updateStatusRow();
            return;
        }
        scheduleViolationRefresh(r, c);
        repaintSelection();
        repaintSymbols();
        updateStatusRow();
    }

    function onBoardClick(ev) {
        // Selection is locked while a hint is on screen.
        if (state.hint) return;
        const target = ev.target.closest('rect.cell-hover');
        if (!target) return;
        const r = parseInt(target.getAttribute('data-r'), 10);
        const c = parseInt(target.getAttribute('data-c'), 10);
        selectCell(r, c);
    }

    function onKeyDown(ev) {
        if (!state.puzzle) return;
        // Ignore key strokes when modifier keys other than Shift are held
        // — leaves the browser's own shortcuts (Ctrl+R, ⌘+L…) alone.
        if (ev.ctrlKey || ev.metaKey || ev.altKey) return;

        const k = ev.key;
        if (k === 'ArrowUp')    { moveSelection(-1, 0); ev.preventDefault(); return; }
        if (k === 'ArrowDown')  { moveSelection( 1, 0); ev.preventDefault(); return; }
        if (k === 'ArrowLeft')  { moveSelection( 0, -1); ev.preventDefault(); return; }
        if (k === 'ArrowRight') { moveSelection( 0,  1); ev.preventDefault(); return; }

        if (k === 'Backspace' || k === 'Delete' || k === '0') {
            eraseSelected();
            ev.preventDefault();
            return;
        }
        if (k === 'n' || k === 'N') {
            toggleNotesMode();
            ev.preventDefault();
            return;
        }
        if (k === 'Escape') {
            state.selected = null;
            repaintSelection();
            ev.preventDefault();
            return;
        }
        // Digit input: 1..N. (We never want a digit larger than the
        // board size to be entered — pressing 7 on a 6×6 board is a
        // no-op.)
        if (k >= '1' && k <= '9') {
            const d = parseInt(k, 10);
            if (d <= state.puzzle.size) {
                onKeypadDigit(d);
                ev.preventDefault();
            }
        }
    }

    function toggleNotesMode() {
        state.notesMode = !state.notesMode;
        updateKeypadMode();
    }

    // Temporary debug affordance: `?sudoku_demo=<technique>` (e.g.
    // ?sudoku_demo=xyWing) makes New Game hunt for a hard puzzle that
    // actually uses that technique, fill in every step up to it, and pop
    // the corresponding hint — so you can eyeball an advanced hint in the
    // real game without playing the whole puzzle by hand.
    const DEMO_TECH = (function () {
        try {
            return new URL(location.href).searchParams.get('sudoku_demo') || '';
        } catch (e) { return ''; }
    })();

    function findDemoPuzzle(N, tech) {
        const gen = window.PuzzleGenerators.sudoku;
        for (let i = 0; i < 200; i++) {
            const seed = (Math.random() * 0xffffffff) >>> 0;
            const pz = gen(N, 'hard', seed);
            if ((pz.stats.techniqueCounts || {})[tech] > 0) return pz;
        }
        return null;
    }

    // Advance the board (mirroring the solver's placements) until the
    // solver's next step is `tech`, then present that step as a hint.
    function demoShow(tech) {
        if (!state.puzzle) return;
        const S = window.PuzzleSolvers && window.PuzzleSolvers.sudoku;
        if (!S) return;
        const N = state.puzzle.size;
        const st = S.makeState(state.puzzle.prefilled, N,
            state.puzzle.boxRows, state.puzzle.boxCols);
        const hard = S.TECHNIQUES_BY_DIFFICULTY.hard;
        let target = null;
        let guard = N * N * N + 50;
        while (guard-- > 0) {
            const step = S.nextStep(st, hard);
            if (!step) break;
            if (step.technique === tech) {
                target = { step, cands: st.cands.map((row) => row.slice()) };
                break;
            }
            for (const p of step.placements) {
                if (!isPrefilled(p.r, p.c)) state.placements[p.r][p.c] = p.value;
            }
            S.applyStep(st, step);
        }
        if (!target) {
            // Never reached (e.g. technique doesn't occur at this size).
            // Reset the fast-forwarded board so we don't leave it solved.
            ensurePlacementsForCurrent();
            recomputeViolations();
            repaintSymbols();
            console.warn(`[sudoku demo] "${tech}" not reached — try 9×9.`);
            return;
        }
        recomputeViolations();
        // Pencil in candidates for just the cells the demo step touches, then
        // commit its eliminations — same as a normal elimination hint, so
        // pressing Hint again continues from here.
        const basic = st.cands.map((row) => row.slice());
        fillStepNotes(target.step, basic);
        for (const e of target.step.eliminations) {
            state.notes[e.r][e.c].delete(e.d);
        }
        setHint({ kind: 'step', step: target.step });
    }

    function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        if (DEMO_TECH) {
            state.puzzle = findDemoPuzzle(shell.size, DEMO_TECH)
                || generatePuzzle(shell.size, 'hard', seed);
        } else {
            state.puzzle = generatePuzzle(shell.size, shell.difficulty, seed);
        }
        ensurePlacementsForCurrent();
        renderBoard();
        buildKeypad();
        clearHint();
        updateStatusRow();
        if (DEMO_TECH) demoShow(DEMO_TECH);
    }

    function resetPlacements() {
        if (!state.puzzle) return;
        ensurePlacementsForCurrent();
        state.won = false;
        clearHint();
        repaintSelection();
        repaintSymbols();
        updateStatusRow();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'sudoku',
            difficulty: { default: 'medium' },
            size: { kind: 'segmented', default: 6 },
            onNewGame: startNewGame,
            onReset: resetPlacements,
            onReveal: repaintSymbols,
        });
        board = shell.dom.board;
        keypad = document.getElementById('keypad');
        board.addEventListener('click', onBoardClick);

        state.hintBanner = document.getElementById('hint-banner');
        const hintBtn = document.getElementById('hint-btn');
        if (hintBtn) hintBtn.addEventListener('click', showHint);

        // Re-render the hint banner if the locale flips while a hint is
        // on screen, so the technique wording follows the language.
        if (PC.i18n && typeof PC.i18n.subscribe === 'function') {
            PC.i18n.subscribe(() => { if (state.hint) renderHintBanner(); });
        }

        // Keyboard input is captured globally; we don't require the SVG
        // to be focused because it's awkward to focus a `<svg>` reliably
        // across browsers.
        window.addEventListener('keydown', onKeyDown);
        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
