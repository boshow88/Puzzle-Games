/**
 * Sudoku — gameplay, dummy puzzle generation, and SVG rendering.
 *
 * Same architectural shape as queens.js / tango.js (deliberately, so the
 * shared parts can be refactored after all four games settle). Only
 * depends on window.PuzzleCommon.
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
 *   }
 *
 * The current generator is intentionally simple: it produces a random
 * legal solution via row/col/box-constrained backtracking, then keeps a
 * fraction of cells as clues. It does NOT guarantee a unique solution
 * and has no proper difficulty calibration; difficulty only controls
 * the clue count.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const BOARD_SIZE = 480;
    const VIOLATION_DELAY_MS = 800;

    /** Box dimensions per board size (rows × cols of a single box). */
    const BOX_SHAPE = {
        6: { rows: 2, cols: 3 },
        9: { rows: 3, cols: 3 },
    };

    /**
     * Fraction of cells to keep as clues, indexed by size then difficulty.
     * Tuned by eyeballing — proper difficulty modelling will arrive with
     * the real generator.
     */
    const CLUE_FRACTION = {
        6: { easy: 0.62, medium: 0.46, hard: 0.36 },
        9: { easy: 0.50, medium: 0.40, hard: 0.32 },
    };

    // -----------------------------------------------------------------
    // Dummy puzzle generator
    // -----------------------------------------------------------------

    /**
     * Build a random valid Sudoku solution grid via randomised
     * backtracking with row / column / box constraints. Returns
     * int[N][N] of 1..N, or null if the search ran out of room.
     */
    function placeValidGrid(N, boxRows, boxCols, rng) {
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        const rowMask = new Array(N).fill(0);
        const colMask = new Array(N).fill(0);
        const boxMask = new Array(N).fill(0);

        function boxIndex(r, c) {
            return Math.floor(r / boxRows) * Math.floor(N / boxCols)
                 + Math.floor(c / boxCols);
        }

        function bit(d) { return 1 << (d - 1); }

        function digitsForCell(r, c) {
            const used = rowMask[r] | colMask[c] | boxMask[boxIndex(r, c)];
            const out = [];
            for (let d = 1; d <= N; d++) {
                if ((used & bit(d)) === 0) out.push(d);
            }
            return PC.rng.shuffle(out, rng);
        }

        function solve(idx) {
            if (idx === N * N) return true;
            const r = Math.floor(idx / N);
            const c = idx % N;
            const b = boxIndex(r, c);
            for (const d of digitsForCell(r, c)) {
                grid[r][c] = d;
                const m = bit(d);
                rowMask[r] |= m; colMask[c] |= m; boxMask[b] |= m;
                if (solve(idx + 1)) return true;
                grid[r][c] = 0;
                rowMask[r] &= ~m; colMask[c] &= ~m; boxMask[b] &= ~m;
            }
            return false;
        }

        return solve(0) ? grid : null;
    }

    /**
     * Keep ~fraction of cells as clues. The remaining cells start empty.
     * Returns int[N][N] (0 / digit). Always keeps at least 1 clue per
     * row to avoid totally empty rows visually.
     */
    function chooseClues(N, solution, fraction, rng) {
        const out = Array.from({ length: N }, () => new Array(N).fill(0));
        const all = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) all.push([r, c]);
        }
        PC.rng.shuffle(all, rng);
        const take = Math.max(N, Math.round(all.length * fraction));
        for (let i = 0; i < take; i++) {
            const [r, c] = all[i];
            out[r][c] = solution[r][c];
        }
        return out;
    }

    function generatePuzzle(size, difficulty, seed) {
        const rng = PC.rng.make(seed);
        const { rows: boxRows, cols: boxCols } = BOX_SHAPE[size];

        let solution = null;
        for (let i = 0; i < 8 && !solution; i++) {
            solution = placeValidGrid(size, boxRows, boxCols, rng);
        }
        if (!solution) {
            // Vanishingly rare with these sizes; fall back to a trivial
            // shifted grid that still satisfies the constraints.
            solution = fallbackGrid(size, boxRows, boxCols);
        }

        const fractionTable = CLUE_FRACTION[size] || CLUE_FRACTION[9];
        const fraction = fractionTable[difficulty] || fractionTable.medium;
        const prefilled = chooseClues(size, solution, fraction, rng);

        return {
            id: `sudoku-${size}x${size}-${difficulty}-${seed.toString(36)}`,
            game: 'sudoku',
            size,
            difficulty,
            boxRows,
            boxCols,
            prefilled,
            solution,
        };
    }

    /** Build a trivially valid Sudoku grid (rotated row scheme). */
    function fallbackGrid(N, boxRows, boxCols) {
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                grid[r][c] = ((boxCols * (r % boxRows) + Math.floor(r / boxRows) + c) % N) + 1;
            }
        }
        return grid;
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

        // Layer: cell backgrounds (white; prefilled get a darker tint).
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

        // Layer: selection backdrop (rebuilt every time the selected cell
        // changes; lives between the background and the box borders so
        // the thick lines stay visible).
        const selectGroup = PC.svgEl('g', { class: 'select' });
        selectGroup.setAttribute('id', 'select');
        svg.appendChild(selectGroup);

        // Layer: box borders (thick lines between Sudoku boxes) + outer
        // frame. All use the shared `.region-border` style so the visual
        // weight matches Queens and Tango.
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
        // Inner box lines.
        for (let r = boxRows; r < N; r += boxRows) {
            addBorder(0, r * cs, W, r * cs);
        }
        for (let c = boxCols; c < N; c += boxCols) {
            addBorder(c * cs, 0, c * cs, W);
        }
        svg.appendChild(borderGroup);

        // Layer: symbols + notes + violations + reveal hint.
        const symbolGroup = PC.svgEl('g', { class: 'symbols' });
        symbolGroup.setAttribute('id', 'symbols');
        svg.appendChild(symbolGroup);

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
        repaintSymbols();
    }

    /** Redraw only the selection-tint layer. Cheap and called on every
     *  selection change / arrow-key navigation. */
    function repaintSelection() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const group = board.querySelector('#select');
        if (!group) return;
        while (group.firstChild) group.removeChild(group.firstChild);

        const sel = state.selected;
        if (!sel) return;

        const selDigit = effective(sel.r, sel.c);
        const selBox = boxIndexOf(sel.r, sel.c);

        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const isFocus = (r === sel.r && c === sel.c);
                const isPeer = (r === sel.r || c === sel.c || boxIndexOf(r, c) === selBox);
                const isSameDigit = selDigit !== 0 && effective(r, c) === selDigit;
                let cls = null;
                if (isFocus) cls = 'cell-select focus';
                else if (isSameDigit) cls = 'cell-select same';
                else if (isPeer) cls = 'cell-select peer';
                if (!cls) continue;
                group.appendChild(PC.svgEl('rect', {
                    class: cls,
                    x: c * cs, y: r * cs, width: cs, height: cs,
                }));
            }
        }
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
                    // Notes: lay them out in a sub-grid matching the box
                    // shape (so 9×9 → 3×3, 6×6 → 2×3 with digits 1–6).
                    const notes = state.notes[r][c];
                    if (notes.size === 0) continue;
                    for (const d of notes) {
                        const nr = Math.floor((d - 1) / boxCols);
                        const nc = (d - 1) % boxCols;
                        const nx = c * cs + cs * (nc + 0.5) / boxCols;
                        const ny = r * cs + cs * (nr + 0.5) / boxRows;
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

        // Reveal: tiny solution digit in the top-left corner of every
        // player-editable cell (prefilled cells already show the answer).
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
        notesBtn = PC.el('button', {
            type: 'button',
            class: 'keypad-btn notes-toggle',
            'aria-pressed': 'false',
            'aria-label': 'Toggle pencil-mark notes mode',
            title: 'Toggle pencil-mark notes (N)',
        }, '✎ Notes');
        notesBtn.addEventListener('click', toggleNotesMode);
        actions.appendChild(notesBtn);

        const eraseBtn = PC.el('button', {
            type: 'button',
            class: 'keypad-btn erase',
            'aria-label': 'Erase',
            title: 'Erase (Backspace / Delete / 0)',
        }, '⌫ Erase');
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

    function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = generatePuzzle(shell.size, shell.difficulty, seed);
        ensurePlacementsForCurrent();
        renderBoard();
        buildKeypad();
        updateStatusRow();
    }

    function resetPlacements() {
        if (!state.puzzle) return;
        ensurePlacementsForCurrent();
        state.won = false;
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
