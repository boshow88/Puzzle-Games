/**
 * Tango puzzle generator — constructive, logic-solvable.
 *
 * Strategy
 * --------
 * 1. Sample a random complete legal solution by randomised backtracking.
 * 2. Seed a small number of `=` / `×` walls compatible with that solution.
 * 3. Starting from the fully-filled board, run a backward loop:
 *      a) If any currently-filled cell would be uniquely determined by
 *         the player's L1 deduction rules after we hide it → hide it.
 *      b) Otherwise, look for an extra wall we could add such that
 *         hiding *some* cell becomes L1-deducible → add the wall and
 *         hide a cell.
 *      c) Otherwise, freeze the remaining filled cells as prefill.
 *
 * This guarantees the resulting puzzle is solvable using only L1
 * tactics (player's perspective; see docs/rules.md). v1 treats all
 * difficulties as L1-only — Medium / Hard parity will arrive when we
 * implement L3/L4 tactics.
 *
 * "L1" tactic set (see also docs/rules.md):
 *   T-count   : a row or column already has N/2 of one symbol → every
 *               empty cell in that row/col must be the other.
 *   T-three   : no three identical symbols may appear consecutively, so
 *               a cell flanked by two of the same value (immediate
 *               neighbours or one neighbour + one over) is forced.
 *   T-wall    : a `=` or `×` wall to a known neighbour forces the cell.
 *
 * Output JSON contract matches the original dummy generator (see
 * tango.js header comment).
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;
    const SUN = 1;
    const MOON = 2;

    // -----------------------------------------------------------------
    // Random complete solution (randomised backtracking).
    // -----------------------------------------------------------------

    function randomSolution(N, rng) {
        const half = N / 2;
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        const rowSun = new Array(N).fill(0);
        const rowMoon = new Array(N).fill(0);
        const colSun = new Array(N).fill(0);
        const colMoon = new Array(N).fill(0);

        function fits(r, c, v) {
            if (v === SUN) {
                if (rowSun[r] >= half || colSun[c] >= half) return false;
            } else {
                if (rowMoon[r] >= half || colMoon[c] >= half) return false;
            }
            if (c >= 2 && grid[r][c - 1] === v && grid[r][c - 2] === v) return false;
            if (r >= 2 && grid[r - 1][c] === v && grid[r - 2][c] === v) return false;
            return true;
        }
        function set(r, c, v) {
            grid[r][c] = v;
            if (v === SUN) { rowSun[r]++; colSun[c]++; }
            else { rowMoon[r]++; colMoon[c]++; }
        }
        function unset(r, c, v) {
            grid[r][c] = 0;
            if (v === SUN) { rowSun[r]--; colSun[c]--; }
            else { rowMoon[r]--; colMoon[c]--; }
        }
        function solve(idx) {
            if (idx === N * N) return true;
            const r = Math.floor(idx / N);
            const c = idx % N;
            const choices = [SUN, MOON];
            PC.rng.shuffle(choices, rng);
            for (const v of choices) {
                if (!fits(r, c, v)) continue;
                set(r, c, v);
                if (solve(idx + 1)) return true;
                unset(r, c, v);
            }
            return false;
        }
        return solve(0) ? grid : null;
    }

    // -----------------------------------------------------------------
    // Walls — list helpers + adjacency map.
    //
    // We store walls in two parallel structures: an array (which goes
    // straight into the puzzle JSON) and a Map keyed by cellKey(r, c)
    // → array of { kind, otherR, otherC } so L1's "wall to known
    // neighbour" check is O(1) per cell.
    // -----------------------------------------------------------------

    function cellKey(r, c) { return r * 100 + c; }
    function wallKey(r1, c1, r2, c2) {
        // Canonical: smaller (r, c) first. The caller already guarantees
        // it but we re-canonicalise to be safe.
        if (r1 > r2 || (r1 === r2 && c1 > c2)) {
            return wallKey(r2, c2, r1, c1);
        }
        return `${r1},${c1}-${r2},${c2}`;
    }

    function buildWallIndex(walls) {
        const byCell = new Map();
        const seen = new Set();
        for (const w of walls) {
            seen.add(wallKey(w.r1, w.c1, w.r2, w.c2));
            const a = cellKey(w.r1, w.c1);
            const b = cellKey(w.r2, w.c2);
            if (!byCell.has(a)) byCell.set(a, []);
            if (!byCell.has(b)) byCell.set(b, []);
            byCell.get(a).push({ kind: w.kind, otherR: w.r2, otherC: w.c2 });
            byCell.get(b).push({ kind: w.kind, otherR: w.r1, otherC: w.c1 });
        }
        return { byCell, seen };
    }

    function adjacentPairs(N) {
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (c + 1 < N) out.push([r, c, r, c + 1]);
                if (r + 1 < N) out.push([r, c, r + 1, c]);
            }
        }
        return out;
    }

    // -----------------------------------------------------------------
    // L1 deduction
    //
    // Given the current `filled` board (1/2/0) and the wall index,
    // does L1 force a value at (r, c)? Returns SUN / MOON / 0.
    //
    // Precondition: filled[r][c] === 0 (i.e. ask "could the player
    // deduce this empty cell").
    // -----------------------------------------------------------------

    function l1ForcedAt(r, c, filled, wallIndex, N) {
        const half = N / 2;

        // T-count along the row.
        let rs = 0, rm = 0;
        for (let j = 0; j < N; j++) {
            if (filled[r][j] === SUN) rs++;
            else if (filled[r][j] === MOON) rm++;
        }
        if (rs >= half) return MOON;
        if (rm >= half) return SUN;

        // T-count along the column.
        let cs = 0, cm = 0;
        for (let i = 0; i < N; i++) {
            if (filled[i][c] === SUN) cs++;
            else if (filled[i][c] === MOON) cm++;
        }
        if (cs >= half) return MOON;
        if (cm >= half) return SUN;

        // T-three horizontally. Three patterns:
        //   [c-2][c-1][_]   two-same to the left
        //   [c-1][_][c+1]   sandwich (two-same straddling this cell)
        //   [_][c+1][c+2]   two-same to the right
        if (c >= 2) {
            const a = filled[r][c - 1], b = filled[r][c - 2];
            if (a !== 0 && a === b) return a === SUN ? MOON : SUN;
        }
        if (c >= 1 && c + 1 < N) {
            const a = filled[r][c - 1], b = filled[r][c + 1];
            if (a !== 0 && a === b) return a === SUN ? MOON : SUN;
        }
        if (c + 2 < N) {
            const a = filled[r][c + 1], b = filled[r][c + 2];
            if (a !== 0 && a === b) return a === SUN ? MOON : SUN;
        }

        // T-three vertically (same shape).
        if (r >= 2) {
            const a = filled[r - 1][c], b = filled[r - 2][c];
            if (a !== 0 && a === b) return a === SUN ? MOON : SUN;
        }
        if (r >= 1 && r + 1 < N) {
            const a = filled[r - 1][c], b = filled[r + 1][c];
            if (a !== 0 && a === b) return a === SUN ? MOON : SUN;
        }
        if (r + 2 < N) {
            const a = filled[r + 1][c], b = filled[r + 2][c];
            if (a !== 0 && a === b) return a === SUN ? MOON : SUN;
        }

        // T-wall: a `=` / `×` wall to a known neighbour.
        const adj = wallIndex.byCell.get(cellKey(r, c));
        if (adj) {
            for (const { kind, otherR, otherC } of adj) {
                const v = filled[otherR][otherC];
                if (v === 0) continue;
                if (kind === 'same') return v;
                return v === SUN ? MOON : SUN;
            }
        }
        return 0;
    }

    /**
     * Enumerate every currently-filled cell whose value the player can
     * deduce via L1 once it's hidden. Returns array of [r, c].
     *
     * O(N^4) worst case: cell scan × row/col scan inside l1ForcedAt.
     * For N ≤ 10 that's 10^4 = trivial.
     */
    function findL1ErasableCells(filled, wallIndex, N) {
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = filled[r][c];
                if (v === 0) continue;
                filled[r][c] = 0;
                const forced = l1ForcedAt(r, c, filled, wallIndex, N);
                filled[r][c] = v;
                if (forced === v) out.push([r, c]);
            }
        }
        return out;
    }

    // -----------------------------------------------------------------
    // Wall addition
    //
    // Find walls we could add (compatible with the solution) such that
    // a new L1-erasable cell appears. Returns array of
    //   { wall, erasable: [[r,c], ...] }
    // -----------------------------------------------------------------

    function findWallAddCandidates(filled, walls, wallIndex, solution, N) {
        const out = [];
        const pairs = adjacentPairs(N);
        for (const [r1, c1, r2, c2] of pairs) {
            const key = wallKey(r1, c1, r2, c2);
            if (wallIndex.seen.has(key)) continue;
            const kind = solution[r1][c1] === solution[r2][c2] ? 'same' : 'diff';
            const newWall = { r1, c1, r2, c2, kind };

            walls.push(newWall);
            const a = cellKey(r1, c1), b = cellKey(r2, c2);
            if (!wallIndex.byCell.has(a)) wallIndex.byCell.set(a, []);
            if (!wallIndex.byCell.has(b)) wallIndex.byCell.set(b, []);
            wallIndex.byCell.get(a).push({ kind, otherR: r2, otherC: c2 });
            wallIndex.byCell.get(b).push({ kind, otherR: r1, otherC: c1 });
            wallIndex.seen.add(key);

            const erasable = findL1ErasableCells(filled, wallIndex, N);

            wallIndex.byCell.get(a).pop();
            wallIndex.byCell.get(b).pop();
            wallIndex.seen.delete(key);
            walls.pop();

            if (erasable.length > 0) {
                out.push({ wall: newWall, erasable });
            }
        }
        return out;
    }

    // -----------------------------------------------------------------
    // Seed walls — sprinkle a handful of walls compatible with the
    // solution before the main erase loop. Keeps Easy puzzles from
    // ending up with zero walls when L1 erases freely without ever
    // needing help.
    // -----------------------------------------------------------------

    function seedWalls(solution, rng, budget, N) {
        const slots = adjacentPairs(N);
        PC.rng.shuffle(slots, rng);
        const walls = [];
        const take = Math.min(budget, slots.length);
        for (let i = 0; i < take; i++) {
            const [r1, c1, r2, c2] = slots[i];
            const kind = solution[r1][c1] === solution[r2][c2] ? 'same' : 'diff';
            walls.push({ r1, c1, r2, c2, kind });
        }
        return walls;
    }

    // -----------------------------------------------------------------
    // Self-check: simulate the player applying L1 until convergence and
    // verify it reaches the solution. If this ever fails the generator
    // has a bug — every cell we erased should be L1-recoverable.
    // -----------------------------------------------------------------

    function verifyL1Solvable(prefilled, walls, solution, N) {
        const filled = prefilled.map((row) => row.slice());
        const wallIndex = buildWallIndex(walls);
        let progressed = true;
        while (progressed) {
            progressed = false;
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (filled[r][c] !== 0) continue;
                    const v = l1ForcedAt(r, c, filled, wallIndex, N);
                    if (v !== 0) {
                        filled[r][c] = v;
                        progressed = true;
                    }
                }
            }
        }
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (filled[r][c] !== solution[r][c]) return false;
            }
        }
        return true;
    }

    // -----------------------------------------------------------------
    // Difficulty tunables — for now just adjusts wall seed budget.
    // Real difficulty differentiation needs L3/L4 (Phase C todo).
    // -----------------------------------------------------------------

    function difficultyParams(N, difficulty) {
        // Seed walls scale roughly with N. The numbers are rough first
        // guesses; eyeball after the first few playthroughs.
        const base = Math.max(1, Math.floor(N / 3));
        if (difficulty === 'easy')   return { wallBudget: base + 1 };
        if (difficulty === 'hard')   return { wallBudget: base - 1 };
        return { wallBudget: base };  // medium
    }

    // -----------------------------------------------------------------
    // Main entry point.
    // -----------------------------------------------------------------

    function generate(size, difficulty, seed) {
        const N = size;
        const rng = PC.rng.make(seed);

        let solution = null;
        for (let attempt = 0; attempt < 8 && !solution; attempt++) {
            solution = randomSolution(N, rng);
        }
        if (!solution) {
            // Vanishingly rare. Fall back to a stripe pattern so the UI
            // still gets a playable shape.
            solution = Array.from({ length: N }, (_, r) =>
                Array.from({ length: N }, (_, c) =>
                    ((r + c) % 2 === 0 ? SUN : MOON)));
        }

        const params = difficultyParams(N, difficulty);
        const filled = solution.map((row) => row.slice());
        const walls = seedWalls(solution, rng, params.wallBudget, N);
        let wallIndex = buildWallIndex(walls);

        const maxIters = N * N * 4;
        for (let iter = 0; iter < maxIters; iter++) {
            const erasable = findL1ErasableCells(filled, wallIndex, N);
            if (erasable.length > 0) {
                const [r, c] = erasable[Math.floor(rng() * erasable.length)];
                filled[r][c] = 0;
                continue;
            }
            const wallChoices =
                findWallAddCandidates(filled, walls, wallIndex, solution, N);
            if (wallChoices.length > 0) {
                const pick = wallChoices[Math.floor(rng() * wallChoices.length)];
                walls.push(pick.wall);
                // Rebuild rather than incrementally patch — the cost is
                // tiny and it keeps the index invariant trivially.
                wallIndex = buildWallIndex(walls);
                const [r, c] = pick.erasable[Math.floor(rng() * pick.erasable.length)];
                filled[r][c] = 0;
                continue;
            }
            break;
        }

        const puzzle = {
            id: `tango-${N}x${N}-${difficulty}-${seed.toString(36)}`,
            game: 'tango',
            size: N,
            difficulty,
            prefilled: filled,
            walls,
            solution,
        };
        if (!verifyL1Solvable(filled, walls, solution, N)) {
            console.warn('[tango-gen] L1 self-check failed for', puzzle.id);
        }
        return puzzle;
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.tango = generate;
})(window);
