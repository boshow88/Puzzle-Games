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
     *  known cells `line` (Int8Array of 0/1/2), return
     *    { and, or, runMin[], runMax[] }
     *  where `and` = cells filled in every arrangement, `or` = filled in at
     *  least one, and runMin[j] / runMax[j] = the earliest / latest start index
     *  of run j across all arrangements (used by the overlap-based tiers).
     *  Returns null if no arrangement fits (a contradiction). */
    function lineAnalyze(runs, L, line) {
        const full = (1 << L) - 1;
        const k = runs.length;
        let andMask = full, orMask = 0, count = 0;
        const runMin = new Array(k).fill(Infinity);
        const runMax = new Array(k).fill(-1);
        const starts = new Array(k);

        (function rec(ri, pos, mask) {
            if (ri === k) {
                // No runs left → every remaining cell must be blank.
                for (let i = pos; i < L; i++) if (line[i] === FILL) return;
                andMask &= mask; orMask |= mask; count++;
                for (let j = 0; j < k; j++) {
                    if (starts[j] < runMin[j]) runMin[j] = starts[j];
                    if (starts[j] > runMax[j]) runMax[j] = starts[j];
                }
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
                starts[ri] = s;
                rec(ri + 1, sep + 1, mask | ((((1 << len) - 1)) << s));
            }
        })(0, 0, 0);

        if (count === 0) return null;
        return { and: andMask, or: orMask, runMin, runMax };
    }

    /** Thin wrapper: just the { and, or } fill bitmasks (full line solver). */
    function lineMasks(runs, L, line) {
        const a = lineAnalyze(runs, L, line);
        return a ? { and: a.and, or: a.or } : null;
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
    // Tiered single-line techniques (easy → hard), nested so that
    //   tier 3 (full) ⊇ tier 2 (L/R overlap) ⊇ tier 1 (pure overlap).
    //   • Tier 1 "basic"  — pure overlap from the clue + line length only
    //                       (ignores current marks); fills only. Marks-
    //                       independent, so it's cached per (clue, L).
    //   • Tier 2 "L/R"    — each run's earliest/latest start *given the
    //                       current marks*; a cell is filled if the SAME run
    //                       covers it in both extremes, blank if no run can
    //                       reach it (anchoring / segmentation).
    //   • Tier 3 "full"   — full enumeration: a cell filled in EVERY arrangement
    //                       (possibly by different runs), the complete solver.
    // -----------------------------------------------------------------

    /** Per-run overlap fill mask: union over runs of [latestStart .. earliestEnd]. */
    function runOverlapMask(a, runs) {
        let mask = 0;
        for (let j = 0; j < runs.length; j++) {
            const lo = a.runMax[j];
            const hi = a.runMin[j] + runs[j] - 1;
            for (let i = lo; i <= hi; i++) mask |= (1 << i);
        }
        return mask;
    }

    // Tier-1 masks depend only on (clue, L), so cache them across the whole run.
    const _basicCache = new Map();
    function basicMasks(runs, L) {
        const key = L + '|' + runs.join(',');
        let v = _basicCache.get(key);
        if (v !== undefined) return v;
        const a = lineAnalyze(runs, L, new Int8Array(L));
        const fullMask = (1 << L) - 1;
        v = a ? { fill: runOverlapMask(a, runs), blank: (~a.or) & fullMask } : { fill: 0, blank: 0 };
        _basicCache.set(key, v);
        return v;
    }

    /** Forced { fill, blank } bitmasks for a single tier (1 / 2 / 3), or null on
     *  contradiction (tiers 2–3 only; tier 1 never contradicts). */
    function tierMasks(tier, runs, L, line) {
        if (tier === 1) return basicMasks(runs, L);
        const a = lineAnalyze(runs, L, line);
        if (!a) return null;
        const fullMask = (1 << L) - 1;
        return {
            fill: tier === 2 ? runOverlapMask(a, runs) : a.and,
            blank: (~a.or) & fullMask,
        };
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

    /** Depth signal: run the full-power fixpoint (rows + cols to convergence)
     *  and return the wave number of the LAST cell determined — i.e. how many
     *  alternating row/col rounds the deduction chain needs. */
    function fixpointDepth(rowClues, colClues, N) {
        const grid = new Int8Array(N * N);
        const line = new Int8Array(N);
        let pass = 0, maxPass = 0, changed = true;
        while (changed) {
            changed = false; pass++;
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) line[c] = grid[r * N + c];
                if (lineForced(rowClues[r], N, line) > 0) {
                    for (let c = 0; c < N; c++) if (grid[r * N + c] === UNKNOWN && line[c] !== UNKNOWN) { grid[r * N + c] = line[c]; maxPass = pass; }
                    changed = true;
                }
            }
            for (let c = 0; c < N; c++) {
                for (let r = 0; r < N; r++) line[r] = grid[r * N + c];
                if (lineForced(colClues[c], N, line) > 0) {
                    for (let r = 0; r < N; r++) if (grid[r * N + c] === UNKNOWN && line[r] !== UNKNOWN) { grid[r * N + c] = line[r]; maxPass = pass; }
                    changed = true;
                }
            }
        }
        return maxPass;
    }

    /** Solve by iterating line deductions to a fixpoint, always applying the
     *  *simplest* technique that makes progress and only escalating when the
     *  easier tiers stall. Returns
     *    { solved, grid, contradiction, passes, score, tiers:[n1,n2,n3], maxTier }
     *  where tiers[t] counts cells first forced at tier t+1. `score` is the
     *  difficulty signal: enumeration-needing (tier-3) cells dominate, then
     *  reliance on tier-2 squeezing, then raw depth. `grid0` (optional) seeds
     *  the state (used by hints to continue from the player's marks). */
    function solve(rowClues, colClues, N, grid0) {
        const grid = grid0 ? grid0.slice() : new Int8Array(N * N);
        const line = new Int8Array(N);
        const tiers = [0, 0, 0]; // cells first forced at tier 1 / 2 / 3
        let passes = 0, maxTier = 0, contradiction = false;

        // Apply tier `t` across every row and column once; returns the number of
        // newly determined cells, or -1 on contradiction.
        function sweep(t) {
            let changed = 0;
            for (let orient = 0; orient < 2; orient++) {
                const isRow = orient === 0;
                for (let k = 0; k < N; k++) {
                    for (let i = 0; i < N; i++) line[i] = isRow ? grid[k * N + i] : grid[i * N + k];
                    const clue = isRow ? rowClues[k] : colClues[k];
                    const m = tierMasks(t, clue, N, line);
                    if (!m) return -1;
                    for (let i = 0; i < N; i++) {
                        if (line[i] !== UNKNOWN) continue;
                        const f = (m.fill >> i) & 1, b = (m.blank >> i) & 1;
                        if (f || b) {
                            const val = f ? FILL : BLANK;
                            grid[isRow ? k * N + i : i * N + k] = val;
                            line[i] = val;
                            changed++;
                        }
                    }
                }
            }
            return changed;
        }

        let progressing = true;
        while (progressing && !contradiction) {
            progressing = false;
            for (let t = 1; t <= 3; t++) {
                const ch = sweep(t);
                if (ch < 0) { contradiction = true; break; }
                if (ch > 0) {
                    passes++;
                    tiers[t - 1] += ch;
                    if (t > maxTier) maxTier = t;
                    progressing = true;
                    break; // a change may re-enable simpler tiers → restart at tier 1
                }
            }
        }

        let solved = !contradiction;
        for (let i = 0; i < N * N && solved; i++) if (grid[i] === UNKNOWN) solved = false;

        // Depth: alternating row/col waves the full-power fixpoint needs (chain
        // length). Folded in so Hard favours deep "back-and-forth" grinders on
        // top of squeeze reliance; enumeration (tier 3) still dominates when present.
        const depth = solved ? fixpointDepth(rowClues, colClues, N) : 0;
        const score = tiers[2] * 100 + tiers[1] * 2 + depth * 6;

        return { solved, grid, contradiction, passes, score, tiers, maxTier, depth };
    }

    /** One hint step from the player's current grid, preferring the simplest
     *  technique: the first row/col where tier 1 forces a new cell, else tier 2,
     *  else tier 3. Returns { orient:'row'|'col', index, clue, cells:[{r,c,state}],
     *  tier, ...reasoning } (see annotateStep) or null if nothing is deducible. */
    function nextStep(rowClues, colClues, N, grid) {
        const line = new Int8Array(N);
        const scanTier = (tier) => {
            for (let orient = 0; orient < 2; orient++) {
                const isRow = orient === 0;
                for (let k = 0; k < N; k++) {
                    for (let i = 0; i < N; i++) line[i] = isRow ? grid[k * N + i] : grid[i * N + k];
                    const clue = isRow ? rowClues[k] : colClues[k];
                    const m = tierMasks(tier, clue, N, line);
                    if (!m) continue;
                    const cells = [];
                    for (let i = 0; i < N; i++) {
                        if (line[i] !== UNKNOWN) continue;
                        const f = (m.fill >> i) & 1, b = (m.blank >> i) & 1;
                        if (f || b) {
                            const r = isRow ? k : i, c = isRow ? i : k;
                            cells.push({ r, c, state: f ? FILL : BLANK });
                        }
                    }
                    if (cells.length) return { orient: isRow ? 'row' : 'col', index: k, clue, cells, tier };
                }
            }
            return null;
        };
        const step = scanTier(1) || scanTier(2) || scanTier(3);
        return step ? annotateStep(step, N, grid) : null;
    }

    /** Attach human-readable reasoning to a hint step. For the chosen line we
     *  re-run the full placement analysis (given the player's current marks)
     *  and classify each forced cell:
     *    • a FILLED cell is attributed to the run whose leftmost and rightmost
     *      feasible placements both cover it (the classic overlap) — recorded
     *      in `fillRuns` with that run's left/right spans so the UI can draw
     *      the "slide range" whose overlap is the forced fill;
     *    • a filled cell no single run's overlap explains (rare tier-3 squeeze)
     *      counts as `squeezeFills`;
     *    • a BLANKED cell is one no run can reach → `eliminate`.
     *  Spans are inclusive cell indices along the line. */
    function annotateStep(step, N, grid) {
        const isRow = step.orient === 'row';
        const k = step.index, clue = step.clue;
        const line = new Int8Array(N);
        for (let i = 0; i < N; i++) line[i] = isRow ? grid[k * N + i] : grid[i * N + k];
        const a = lineAnalyze(clue, N, line);
        const runSet = new Map();
        let overlapFills = 0, squeezeFills = 0, eliminate = 0;
        for (const cell of step.cells) {
            if (cell.state !== FILL) { eliminate++; continue; }
            const i = isRow ? cell.c : cell.r;
            let found = -1;
            if (a) for (let j = 0; j < clue.length; j++) {
                if (a.runMax[j] <= i && i <= a.runMin[j] + clue[j] - 1) { found = j; break; }
            }
            if (found >= 0) { overlapFills++; runSet.set(found, true); }
            else squeezeFills++;
        }
        const fillRuns = [];
        if (a) for (const j of runSet.keys()) {
            const len = clue[j];
            fillRuns.push({ len, left: [a.runMin[j], a.runMin[j] + len - 1], right: [a.runMax[j], a.runMax[j] + len - 1] });
        }
        step.fillRuns = fillRuns;
        step.overlapFills = overlapFills;
        step.squeezeFills = squeezeFills;
        step.eliminate = eliminate;
        return step;
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
                if (res.solved) pool.push({ fill, rowClues, colClues, score: res.score, tiers: res.tiers, depth: res.depth });
            }
            if (onProgress && (t & 31) === 0) await onProgress(0.05 + 0.9 * (t + 1) / attempts);
        }
        if (!pool.length) {
            // Extremely unlikely; fall back to a trivially-solvable sparse board.
            const fill = new Uint8Array(N * N); fill[0] = 1;
            const { rowClues, colClues } = deriveClues(fill, N);
            pool.push({ fill, rowClues, colClues, score: 0, tiers: [0, 0, 0], depth: 0 });
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
            stats: { score: chosen.score, poolSize: pool.length, tiers: chosen.tiers, depth: chosen.depth },
        };
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleGenerators.nonogram = generate;
    global.PuzzleSolvers.nonogram = { lineForced, lineMasks, lineAnalyze, tierMasks, solve, nextStep, deriveClues };
    global.PuzzleGenerators.nonogramInternals = { lineMasks, lineAnalyze, tierMasks, basicMasks, runOverlapMask, lineForced, fixpointDepth, solve, nextStep, deriveClues, randomFill, attemptsFor };
})(typeof window !== 'undefined' ? window : this);
