/**
 * Sudoku generator — full-solution + logic-bounded hole-digging.
 *
 * Strategy (mirrors Tango / Queens in spirit: build a solution, then
 * carve it down under a solver that only uses the difficulty's allowed
 * techniques, so the delivered puzzle is guaranteed uniquely solvable
 * by exactly those techniques):
 *
 *   1. Generate a random complete solution via randomised row/col/box
 *      backtracking.
 *   2. Copy it to the clue grid, then visit cells in random order and
 *      try to blank each one. After blanking, run the technique-bounded
 *      solver from the current clue grid: if it still solves the board
 *      completely, the blank is safe (uniqueness preserved) and we keep
 *      it; otherwise we restore the clue.
 *   3. Difficulty controls how far we dig (minimum clue count to keep).
 *      hard digs as far as the technique set allows.
 *
 * Why "solves completely ⇒ unique": every technique here only ever
 * places a *forced* digit (a cell with a single candidate, or a digit
 * with a single home in a unit). A chain of forced moves that fills the
 * grid proves the solution is the only one reachable — hence unique.
 *
 * Techniques (basic singles for now; hard will gain advanced ones later):
 *   - fullHouse    : a unit (row/col/box) with exactly one empty cell.
 *   - nakedSingle  : a cell whose row+col+box leave exactly one digit.
 *   - hiddenSingle : a digit that fits exactly one cell of a unit.
 *
 * Puzzle JSON contract (unchanged from the old inline generator):
 *   { id, game:'sudoku', size:N, difficulty, boxRows, boxCols,
 *     prefilled:int[N][N] (0 empty / 1..N clue), solution:int[N][N],
 *     stats:{ clues, techniqueCounts } }
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    /** Box dimensions per board size (rows × cols of a single box). */
    const BOX_SHAPE = {
        6: { rows: 2, cols: 3 },
        9: { rows: 3, cols: 3 },
    };

    // Techniques allowed per difficulty. All three basic singles for
    // now — difficulty currently differs only by how many clues we
    // keep (see minClues). Hard will gain advanced techniques later,
    // at which point it can be dug further than the basic set allows.
    const TECHNIQUES_BY_DIFFICULTY = {
        easy:   { fullHouse: true, nakedSingle: true, hiddenSingle: true },
        medium: { fullHouse: true, nakedSingle: true, hiddenSingle: true },
        hard:   { fullHouse: true, nakedSingle: true, hiddenSingle: true },
    };

    // Minimum clue count to keep when digging. Lower = harder (fewer
    // givens, more scanning). 0 means "dig as far as the technique set
    // allows" — used by hard so it bottoms out at the singles limit.
    function minClues(N, difficulty) {
        if (N === 6) {
            if (difficulty === 'easy') return 22;
            if (difficulty === 'medium') return 16;
            return 0;
        }
        // 9×9
        if (difficulty === 'easy') return 40;
        if (difficulty === 'medium') return 32;
        return 0;
    }

    function boxDims(N) { return BOX_SHAPE[N] || BOX_SHAPE[9]; }

    function popcount(x) {
        let n = 0;
        while (x) { n += x & 1; x >>>= 1; }
        return n;
    }

    // Digit (1..N) of a mask known to hold exactly one bit.
    function bitToDigit(mask) {
        let d = 1;
        while (mask > 1) { mask >>>= 1; d += 1; }
        return d;
    }

    // -----------------------------------------------------------------
    // Full solution — randomised backtracking with row/col/box masks.
    // -----------------------------------------------------------------

    function placeValidGrid(N, boxRows, boxCols, rng) {
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        const rowMask = new Array(N).fill(0);
        const colMask = new Array(N).fill(0);
        const boxMask = new Array(N).fill(0);
        const boxesPerRow = Math.floor(N / boxCols);

        function boxIndex(r, c) {
            return Math.floor(r / boxRows) * boxesPerRow + Math.floor(c / boxCols);
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

    /** Trivially valid grid (rotated row scheme) — last-ditch fallback. */
    function fallbackGrid(N, boxRows, boxCols) {
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                grid[r][c] = ((boxCols * (r % boxRows)
                    + Math.floor(r / boxRows) + c) % N) + 1;
            }
        }
        return grid;
    }

    // -----------------------------------------------------------------
    // Solver state — the grid plus incremental row/col/box usage masks
    // and precomputed unit cell lists. `grid` is a private copy so the
    // caller's array is never mutated.
    // -----------------------------------------------------------------

    function makeState(grid, N, boxRows, boxCols) {
        const boxesPerRow = Math.floor(N / boxCols);
        const g = grid.map((row) => row.slice());
        const rowMask = new Array(N).fill(0);
        const colMask = new Array(N).fill(0);
        const boxMask = new Array(N).fill(0);
        let filled = 0;

        const boxIndex = (r, c) =>
            Math.floor(r / boxRows) * boxesPerRow + Math.floor(c / boxCols);

        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const d = g[r][c];
                if (d !== 0) {
                    const m = 1 << (d - 1);
                    rowMask[r] |= m; colMask[c] |= m; boxMask[boxIndex(r, c)] |= m;
                    filled += 1;
                }
            }
        }

        // Precompute the cell list of every unit once. Units are indexed
        // 0..N-1 for rows, cols, boxes independently.
        const rows = Array.from({ length: N }, () => []);
        const cols = Array.from({ length: N }, () => []);
        const boxes = Array.from({ length: N }, () => []);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                rows[r].push([r, c]);
                cols[c].push([r, c]);
                boxes[boxIndex(r, c)].push([r, c]);
            }
        }

        return {
            N, boxRows, boxCols, boxIndex,
            grid: g, rowMask, colMask, boxMask, filled,
            rows, cols, boxes,
            fullMask: (1 << N) - 1,
        };
    }

    function place(state, r, c, d) {
        if (state.grid[r][c] !== 0) return;
        state.grid[r][c] = d;
        const m = 1 << (d - 1);
        state.rowMask[r] |= m;
        state.colMask[c] |= m;
        state.boxMask[state.boxIndex(r, c)] |= m;
        state.filled += 1;
    }

    // Candidate bitmask for an empty cell (0 if the cell is filled).
    function candMask(state, r, c) {
        if (state.grid[r][c] !== 0) return 0;
        const used = state.rowMask[r]
            | state.colMask[c]
            | state.boxMask[state.boxIndex(r, c)];
        return state.fullMask & ~used;
    }

    // -----------------------------------------------------------------
    // Technique detectors. Each returns a step descriptor or null.
    //   step = { technique, r, c, value, unitKind, unitIndex }
    // unitKind/unitIndex identify the unit the deduction reads from
    // (null for nakedSingle, which reasons from a cell's three peers).
    // -----------------------------------------------------------------

    function findFullHouse(state) {
        const { N } = state;
        const kinds = [
            ['row', state.rows], ['col', state.cols], ['box', state.boxes],
        ];
        for (const [kind, units] of kinds) {
            for (let u = 0; u < N; u++) {
                const cells = units[u];
                let emptyCell = null;
                let emptyCount = 0;
                let present = 0;
                for (const [r, c] of cells) {
                    const d = state.grid[r][c];
                    if (d === 0) { emptyCell = [r, c]; emptyCount += 1; }
                    else present |= 1 << (d - 1);
                }
                if (emptyCount !== 1) continue;
                const missing = state.fullMask & ~present;
                if (popcount(missing) !== 1) continue; // defensive
                return {
                    technique: 'fullHouse',
                    r: emptyCell[0], c: emptyCell[1],
                    value: bitToDigit(missing),
                    unitKind: kind, unitIndex: u,
                };
            }
        }
        return null;
    }

    function findNakedSingle(state) {
        const { N } = state;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.grid[r][c] !== 0) continue;
                const cm = candMask(state, r, c);
                if (popcount(cm) === 1) {
                    return {
                        technique: 'nakedSingle',
                        r, c, value: bitToDigit(cm),
                        unitKind: null, unitIndex: null,
                    };
                }
            }
        }
        return null;
    }

    function findHiddenSingle(state) {
        const { N } = state;
        const kinds = [
            ['row', state.rows], ['col', state.cols], ['box', state.boxes],
        ];
        for (const [kind, units] of kinds) {
            for (let u = 0; u < N; u++) {
                const cells = units[u];
                // For each digit still missing from this unit, count the
                // empty cells that could hold it. Exactly one ⇒ forced.
                for (let d = 1; d <= N; d++) {
                    const bitD = 1 << (d - 1);
                    let homeCell = null;
                    let homes = 0;
                    let alreadyPlaced = false;
                    for (const [r, c] of cells) {
                        if (state.grid[r][c] === d) { alreadyPlaced = true; break; }
                        if (state.grid[r][c] !== 0) continue;
                        if (candMask(state, r, c) & bitD) {
                            homeCell = [r, c]; homes += 1;
                            if (homes > 1) break;
                        }
                    }
                    if (alreadyPlaced || homes !== 1) continue;
                    return {
                        technique: 'hiddenSingle',
                        r: homeCell[0], c: homeCell[1], value: d,
                        unitKind: kind, unitIndex: u,
                    };
                }
            }
        }
        return null;
    }

    // First applicable step, easiest technique first:
    // fullHouse → nakedSingle → hiddenSingle.
    function nextStep(state, techniques) {
        const t = techniques || TECHNIQUES_BY_DIFFICULTY.hard;
        let s = null;
        if (t.fullHouse) { s = findFullHouse(state); if (s) return s; }
        if (t.nakedSingle) { s = findNakedSingle(state); if (s) return s; }
        if (t.hiddenSingle) { s = findHiddenSingle(state); if (s) return s; }
        return null;
    }

    // Solve as far as the allowed techniques reach. Returns
    // { solved, filled, grid, techniqueCounts }.
    function solveWithTechniques(grid, N, boxRows, boxCols, techniques) {
        const state = makeState(grid, N, boxRows, boxCols);
        const techniqueCounts = { fullHouse: 0, nakedSingle: 0, hiddenSingle: 0 };
        const safety = N * N + 5;
        for (let i = 0; i < safety; i++) {
            const step = nextStep(state, techniques);
            if (!step) break;
            place(state, step.r, step.c, step.value);
            techniqueCounts[step.technique] += 1;
        }
        return {
            solved: state.filled === N * N,
            filled: state.filled,
            grid: state.grid,
            techniqueCounts,
        };
    }

    // -----------------------------------------------------------------
    // Contradiction finder — first unit that contains a duplicate digit.
    // Used by the in-game "you have too many X here" error hint. Reads
    // the caller's grid directly (no state needed).
    // Returns { unitKind, unitIndex, value, cells:[[r,c],...] } or null.
    // -----------------------------------------------------------------

    function findContradiction(grid, N, boxRows, boxCols) {
        const boxesPerRow = Math.floor(N / boxCols);
        const boxIndex = (r, c) =>
            Math.floor(r / boxRows) * boxesPerRow + Math.floor(c / boxCols);
        const units = [];
        for (let i = 0; i < N; i++) {
            units.push({ kind: 'row', index: i, cells: [] });
            units.push({ kind: 'col', index: i, cells: [] });
            units.push({ kind: 'box', index: i, cells: [] });
        }
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                units[r * 3].cells.push([r, c]);
                units[c * 3 + 1].cells.push([r, c]);
                units[boxIndex(r, c) * 3 + 2].cells.push([r, c]);
            }
        }
        for (const unit of units) {
            const seen = new Map();
            for (const [r, c] of unit.cells) {
                const d = grid[r][c];
                if (d === 0) continue;
                if (!seen.has(d)) seen.set(d, []);
                seen.get(d).push([r, c]);
            }
            for (const [d, cells] of seen) {
                if (cells.length > 1) {
                    return {
                        unitKind: unit.kind, unitIndex: unit.index,
                        value: d, cells,
                    };
                }
            }
        }
        return null;
    }

    // -----------------------------------------------------------------
    // Hole-digging — carve the solution down while keeping it uniquely
    // solvable by the allowed techniques.
    // -----------------------------------------------------------------

    function digHoles(solution, N, boxRows, boxCols, techniques, keepMin, rng) {
        const prefilled = solution.map((row) => row.slice());
        const cells = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) cells.push([r, c]);
        }
        PC.rng.shuffle(cells, rng);

        let clues = N * N;
        for (const [r, c] of cells) {
            if (keepMin > 0 && clues <= keepMin) break;
            const saved = prefilled[r][c];
            if (saved === 0) continue;
            prefilled[r][c] = 0;
            const res = solveWithTechniques(prefilled, N, boxRows, boxCols, techniques);
            if (res.solved) {
                clues -= 1;
            } else {
                prefilled[r][c] = saved; // restore — removal broke solvability
            }
        }
        return { prefilled, clues };
    }

    // -----------------------------------------------------------------
    // Public entry point.
    // -----------------------------------------------------------------

    function generate(size, difficulty, seed) {
        const N = size;
        const { rows: boxRows, cols: boxCols } = boxDims(N);
        const rng = PC.rng.make(seed >>> 0);

        let solution = null;
        for (let i = 0; i < 8 && !solution; i++) {
            solution = placeValidGrid(N, boxRows, boxCols, rng);
        }
        if (!solution) solution = fallbackGrid(N, boxRows, boxCols);

        const techniques = TECHNIQUES_BY_DIFFICULTY[difficulty]
            || TECHNIQUES_BY_DIFFICULTY.medium;
        const keepMin = minClues(N, difficulty);
        const { prefilled, clues } = digHoles(
            solution, N, boxRows, boxCols, techniques, keepMin, rng);

        // Record the technique mix of the canonical solve for insight
        // into how the puzzle actually plays out (surfaced in stats).
        const replay = solveWithTechniques(prefilled, N, boxRows, boxCols, techniques);

        return {
            id: `sudoku-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'sudoku',
            size: N,
            difficulty,
            boxRows,
            boxCols,
            prefilled,
            solution,
            stats: {
                clues,
                emptyCells: N * N - clues,
                techniqueCounts: replay.techniqueCounts,
            },
        };
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.sudoku = generate;

    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleSolvers.sudoku = {
        TECHNIQUES_BY_DIFFICULTY,
        placeValidGrid,
        makeState,
        place,
        candMask,
        findFullHouse,
        findNakedSingle,
        findHiddenSingle,
        nextStep,
        solveWithTechniques,
        findContradiction,
    };
})(window);
