/**
 * Nonogram (Picross) — generator + line-logic solver.
 *
 * A Nonogram is an N×N grid where each row/column carries a clue: the ordered
 * run-lengths of its filled cells (e.g. "3 1" = a run of 3, a gap, a run of 1).
 * The player fills cells so every line matches its clue.
 *
 * Design — one mechanism does everything
 * --------------------------------------
 * The core is a *line solver*: for a single line (its clue + current known
 * cells) it finds the cells that are filled in EVERY valid arrangement (force
 * fill) and the cells filled in NO arrangement (force blank). Iterating that
 * over all rows/cols to a fixpoint:
 *   • if it determines every cell, the puzzle is solvable by pure logic — and
 *     therefore has a UNIQUE solution (the deduction never branched), so we get
 *     uniqueness for free and only ship line-solvable boards;
 *   • the solve trace (how many passes, how late each cell was forced) is the
 *     difficulty score the generator bands on;
 *   • the same "next forced line" is the hint the game shows.
 *
 * Exposed:
 *   window.PuzzleGenerators.nonogram(size, difficulty, seed, onProgress)
 *     → { id, game:'nonogram', size, difficulty, rowClues, colClues, solution, stats }
 *   window.PuzzleSolvers.nonogram  — { lineForced, solve, nextStep, deriveClues }
 *   window.PuzzleGenerators.nonogramInternals — for the self-test
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    // Cell states used by the solver: 0 unknown, 1 filled, 2 blank.
    const UNKNOWN = 0, FILL = 1, BLANK = 2;

    // -----------------------------------------------------------------
    // Line solver
    // -----------------------------------------------------------------

    /** Over all arrangements of `runs` on a length-L line consistent with the
     *  known cells `line` (Int8Array of 0/1/2), return { and, or } bitmasks of
     *  the filled cells: `and` = filled in every arrangement, `or` = filled in
     *  at least one. Returns null if no arrangement fits (a contradiction). */
    function lineMasks(runs, L, line) {
        const full = (1 << L) - 1;
        let andMask = full, orMask = 0, count = 0;

        (function rec(ri, pos, mask) {
            if (ri === runs.length) {
                // No runs left → every remaining cell must be blank.
                for (let i = pos; i < L; i++) if (line[i] === FILL) return;
                andMask &= mask; orMask |= mask; count++;
                return;
            }
            const len = runs[ri];
            for (let s = pos; s + len <= L; s++) {
                // Gap pos..s-1 stays blank: a forced-fill cell can't sit there,
                // and sliding s further right only keeps it in the gap → stop.
                let inGapOk = true;
                for (let i = pos; i < s; i++) if (line[i] === FILL) { inGapOk = false; break; }
                if (!inGapOk) break;
                // Run cells s..s+len-1 can't include a forced-blank cell.
                let runOk = true;
                for (let i = s; i < s + len; i++) if (line[i] === BLANK) { runOk = false; break; }
                if (!runOk) continue;
                // The separator after the run can't be a forced-fill cell.
                const sep = s + len;
                if (sep < L && line[sep] === FILL) continue;
                rec(ri + 1, sep + 1, mask | ((((1 << len) - 1)) << s));
            }
        })(0, 0, 0);

        if (count === 0) return null;
        return { and: andMask, or: orMask };
    }

    /** Apply one forced deduction to a line in place. Returns the number of
     *  newly determined cells, or -1 on contradiction. */
    function lineForced(runs, L, line) {
        const m = lineMasks(runs, L, line);
        if (!m) return -1;
        let changed = 0;
        for (let i = 0; i < L; i++) {
            if (line[i] !== UNKNOWN) continue;
            const canFill = (m.or >> i) & 1;
            const mustFill = (m.and >> i) & 1;
            if (mustFill) { line[i] = FILL; changed++; }
            else if (!canFill) { line[i] = BLANK; changed++; }
        }
        return changed;
    }

    // -----------------------------------------------------------------
    // Clues
    // -----------------------------------------------------------------

    /** Run-length clue for one 0/1 line. Empty line → [] (shown as "0"). */
    function lineRuns(cells) {
        const runs = [];
        let run = 0;
        for (const v of cells) {
            if (v) run++;
            else if (run) { runs.push(run); run = 0; }
        }
        if (run) runs.push(run);
        return runs;
    }

    /** Derive { rowClues, colClues } from an N×N fill (Uint8Array row-major). */
    function deriveClues(fill, N) {
        const rowClues = [], colClues = [];
        for (let r = 0; r < N; r++) {
            const row = [];
            for (let c = 0; c < N; c++) row.push(fill[r * N + c]);
            rowClues.push(lineRuns(row));
        }
        for (let c = 0; c < N; c++) {
            const col = [];
            for (let r = 0; r < N; r++) col.push(fill[r * N + c]);
            colClues.push(lineRuns(col));
        }
        return { rowClues, colClues };
    }

    // -----------------------------------------------------------------
    // Full solve (from a starting grid; default empty)
    // -----------------------------------------------------------------

    /** Solve by iterating line deductions to a fixpoint. Returns
     *  { solved, grid, contradiction, passes, score }. `score` rewards cells
     *  that could only be forced in later passes (i.e. needed cross-line
     *  information) — the difficulty signal. `grid0` (optional) seeds the state
     *  (used by hints to continue from the player's marks). */
    function solve(rowClues, colClues, N, grid0) {
        const grid = grid0 ? grid0.slice() : new Int8Array(N * N);
        const setPass = new Int32Array(N * N); // pass each cell was determined on
        const line = new Int8Array(N);
        let pass = 0, changedAny = true, contradiction = false;

        while (changedAny && !contradiction) {
            changedAny = false; pass++;
            // Rows
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) line[c] = grid[r * N + c];
                const ch = lineForced(rowClues[r], N, line);
                if (ch < 0) { contradiction = true; break; }
                if (ch > 0) {
                    for (let c = 0; c < N; c++) {
                        if (grid[r * N + c] === UNKNOWN && line[c] !== UNKNOWN) {
                            grid[r * N + c] = line[c]; setPass[r * N + c] = pass;
                        }
                    }
                    changedAny = true;
                }
            }
            if (contradiction) break;
            // Columns
            for (let c = 0; c < N; c++) {
                for (let r = 0; r < N; r++) line[r] = grid[r * N + c];
                const ch = lineForced(colClues[c], N, line);
                if (ch < 0) { contradiction = true; break; }
                if (ch > 0) {
                    for (let r = 0; r < N; r++) {
                        if (grid[r * N + c] === UNKNOWN && line[r] !== UNKNOWN) {
                            grid[r * N + c] = line[r]; setPass[r * N + c] = pass;
                        }
                    }
                    changedAny = true;
                }
            }
        }

        let solved = !contradiction;
        for (let i = 0; i < N * N && solved; i++) if (grid[i] === UNKNOWN) solved = false;

        // Difficulty: sum of (pass-1) over determined cells + the pass count.
        // First-pass (pure overlap) cells add 0; later cells cost more.
        let score = pass;
        for (let i = 0; i < N * N; i++) if (setPass[i] > 0) score += setPass[i] - 1;

        return { solved, grid, contradiction, passes: pass, score };
    }

    /** One hint step from the player's current grid: the first row/col that can
     *  force at least one new cell. Returns { orient:'row'|'col', index, clue,
     *  cells:[{r,c,state}] } or null if nothing is deducible right now. */
    function nextStep(rowClues, colClues, N, grid) {
        const line = new Int8Array(N);
        const scan = (orient) => {
            for (let k = 0; k < N; k++) {
                for (let i = 0; i < N; i++) line[i] = orient === 'row' ? grid[k * N + i] : grid[i * N + k];
                const before = line.slice();
                const clue = orient === 'row' ? rowClues[k] : colClues[k];
                const ch = lineForced(clue, N, line);
                if (ch > 0) {
                    const cells = [];
                    for (let i = 0; i < N; i++) {
                        if (before[i] === UNKNOWN && line[i] !== UNKNOWN) {
                            cells.push(orient === 'row'
                                ? { r: k, c: i, state: line[i] }
                                : { r: i, c: k, state: line[i] });
                        }
                    }
                    if (cells.length) return { orient, index: k, clue, cells };
                }
            }
            return null;
        };
        return scan('row') || scan('col');
    }

    // -----------------------------------------------------------------
    // Generator
    // -----------------------------------------------------------------

    // Fill density band (fraction of filled cells), sampled per puzzle so the
    // pictures vary. Mid densities give the richest clues.
    function sampleDensity(rng) { return 0.42 + 0.22 * rng(); } // ~0.42–0.64

    function randomFill(N, rng) {
        const p = sampleDensity(rng);
        const fill = new Uint8Array(N * N);
        let filled = 0;
        for (let i = 0; i < N * N; i++) { if (rng() < p) { fill[i] = 1; filled++; } }
        return filled === 0 || filled === N * N ? null : fill;
    }

    // best-of-K pool size — plenty of line-solvable boards exist at these sizes.
    function attemptsFor(N) { return N <= 6 ? 120 : N <= 9 ? 180 : 260; }

    async function generate(size, difficulty, seed, onProgress) {
        const N = size;
        const rng = PC.rng.make(seed >>> 0);
        const attempts = attemptsFor(N);
        if (onProgress) await onProgress(0.05);

        // Collect line-solvable (⇒ unique) candidates, scored by solve depth.
        const pool = [];
        for (let t = 0; t < attempts; t++) {
            const fill = randomFill(N, rng);
            if (fill) {
                const { rowClues, colClues } = deriveClues(fill, N);
                const res = solve(rowClues, colClues, N);
                if (res.solved) pool.push({ fill, rowClues, colClues, score: res.score });
            }
            if (onProgress && (t & 31) === 0) await onProgress(0.05 + 0.9 * (t + 1) / attempts);
        }
        if (!pool.length) {
            // Extremely unlikely; fall back to a trivially-solvable sparse board.
            const fill = new Uint8Array(N * N); fill[0] = 1;
            const { rowClues, colClues } = deriveClues(fill, N);
            pool.push({ fill, rowClues, colClues, score: 0 });
        }

        pool.sort((a, b) => a.score - b.score);
        const idx = difficulty === 'easy' ? 0
            : difficulty === 'hard' ? pool.length - 1
                : Math.floor((pool.length - 1) / 2);
        const chosen = pool[idx];

        if (onProgress) await onProgress(1);

        const solution = [];
        for (let r = 0; r < N; r++) {
            const row = [];
            for (let c = 0; c < N; c++) row.push(chosen.fill[r * N + c] ? 1 : 0);
            solution.push(row);
        }
        return {
            id: `nonogram-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'nonogram', size: N, difficulty,
            rowClues: chosen.rowClues, colClues: chosen.colClues,
            solution,
            stats: { score: chosen.score, poolSize: pool.length },
        };
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleGenerators.nonogram = generate;
    global.PuzzleSolvers.nonogram = { lineForced, lineMasks, solve, nextStep, deriveClues };
    global.PuzzleGenerators.nonogramInternals = { lineMasks, lineForced, solve, nextStep, deriveClues, randomFill, attemptsFor };
})(typeof window !== 'undefined' ? window : this);
