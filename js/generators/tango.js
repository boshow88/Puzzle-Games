/**
 * Tango puzzle generator — constructive, logic-solvable.
 *
 * Strategy
 * --------
 * 1. Sample a random complete legal solution by randomised backtracking.
 * 2. Seed a small number of `=` / `×` walls compatible with that solution.
 * 3. Starting from the fully-filled board, run a backward loop:
 *      a) Try to hide a cell whose value is L1-recoverable from the
 *         remaining state. (Easy / Medium / Hard all do this first.)
 *      b) If L1 stalls AND difficulty allows L3, try to hide a cell
 *         whose value is L3-recoverable but not L1-recoverable.
 *      c) Otherwise, try adding a wall (compatible with the solution)
 *         that immediately creates an L1-erasable cell, then hide it.
 *      d) Otherwise, freeze the remaining filled cells as prefill.
 *
 * The resulting puzzle is guaranteed solvable using only the tactic
 * tiers permitted for its difficulty. The generator self-checks this
 * before returning.
 *
 * Tactic tiers (the underlying game rules they apply are documented in
 * docs/rules.md):
 *   L1   one-glance deductions:
 *     T-count : a row/col already has N/2 of one symbol → every empty
 *               cell in that line must be the other.
 *     T-three : no three identical symbols in a row, so a cell flanked
 *               by two of the same value (immediate neighbours or one
 *               + one over) is forced.
 *     T-wall  : a `=` / `×` wall to a known neighbour forces the cell.
 *   L3   row/col-bounded contradiction:
 *     Assume the opposite at X. If no completion of the line (using
 *     only that line's existing values, internal walls, half-count and
 *     no-three rules) is valid → X is forced. L1 is a strict subset of
 *     L3 in coverage; the two stay separate so the player experience
 *     (and the generator's choice) reflects the cognitive cost.
 *
 * L4 (line + immediately-adjacent cross-line cues) is on the
 * roadmap; not implemented yet.
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
    // L3 deduction — row/column-bounded brute-force.
    //
    // Definition: hide cell X at (r, c). If we focus on EITHER row r OR
    // column c alone — i.e. consider only the values currently visible
    // in that line, the walls internal to that line, the half-count
    // rule, and the no-three-in-a-row rule — and we can prove that
    // assigning the wrong value at X makes the line uncompletable, then
    // X is L3-forced.
    //
    // L1 is a strict subset of L3 (anything L1 fires on, L3 would also
    // fire on by the same logic). We keep them separate for two reasons:
    //   - L1 is O(1) per cell, L3 is O(2^N); always try L1 first.
    //   - The player experience is "I can see this directly" vs "I have
    //     to play forward and check this line", which we want to track.
    //
    // L3 does NOT consider walls that cross out of the line or any
    // information from the other dimension. That extra reach is L4
    // territory (still unimplemented).
    // -----------------------------------------------------------------

    /**
     * Extract the N values along a row or column. orientation: 'row' or
     * 'col'. lineIdx is the row index or column index.
     */
    function extractLine(orientation, lineIdx, filled, N) {
        const out = new Array(N);
        if (orientation === 'row') {
            for (let i = 0; i < N; i++) out[i] = filled[lineIdx][i];
        } else {
            for (let i = 0; i < N; i++) out[i] = filled[i][lineIdx];
        }
        return out;
    }

    /**
     * Extract walls internal to the given line, indexed by position
     * along the line. wallsOnLine[i] is the wall (or null) between
     * positions i and i+1 along the line.
     */
    function lineWalls(orientation, lineIdx, wallIndex, N) {
        const out = new Array(N - 1).fill(null);
        for (let i = 0; i < N - 1; i++) {
            let a, otherR, otherC;
            if (orientation === 'row') {
                a = cellKey(lineIdx, i);
                otherR = lineIdx; otherC = i + 1;
            } else {
                a = cellKey(i, lineIdx);
                otherR = i + 1; otherC = lineIdx;
            }
            const adj = wallIndex.byCell.get(a);
            if (!adj) continue;
            for (const w of adj) {
                if (w.otherR === otherR && w.otherC === otherC) {
                    out[i] = w.kind;
                    break;
                }
            }
        }
        return out;
    }

    /**
     * Can the line be completed (filling the 0 cells) such that the
     * half-count, no-three-in-a-row, and internal walls all hold?
     *
     * Returns true if any valid completion exists. The line array is
     * left unchanged on return (recursion restores it on backtrack).
     */
    function canCompleteLine(line, wallsOnLine, N) {
        const half = N / 2;
        const emptyIdx = [];
        let cs = 0, cm = 0;
        for (let i = 0; i < N; i++) {
            if (line[i] === SUN) cs++;
            else if (line[i] === MOON) cm++;
            else emptyIdx.push(i);
        }
        if (cs > half || cm > half) return false;

        // Validate existing structure once before recursion.
        for (let i = 0; i + 2 < N; i++) {
            if (line[i] !== 0 && line[i] === line[i + 1] && line[i + 1] === line[i + 2]) {
                return false;
            }
        }
        for (let i = 0; i + 1 < N; i++) {
            const w = wallsOnLine[i];
            if (w == null) continue;
            const a = line[i], b = line[i + 1];
            if (a === 0 || b === 0) continue;
            if (w === 'same' && a !== b) return false;
            if (w === 'diff' && a === b) return false;
        }

        // Backtrack over empty positions.
        function ok(k, curSun, curMoon) {
            if (curSun > half || curMoon > half) return false;
            if (k === emptyIdx.length) {
                return curSun === half && curMoon === half;
            }
            const idx = emptyIdx[k];
            for (const v of [SUN, MOON]) {
                line[idx] = v;
                // Local checks involving idx after placement.
                let bad = false;
                // Three-in-a-row windows that CONTAIN idx — i.e. windows
                // starting at s where s <= idx <= s+2. Earlier versions
                // mis-bounded this to "windows ending at idx" and silently
                // accepted recursive placements that created 3-in-a-row
                // with two cells on the right of idx that came from
                // input (not recursion), causing L3 false negatives that
                // broke verifier convergence.
                for (let s = Math.max(0, idx - 2); s <= Math.min(idx, N - 3); s++) {
                    if (line[s] !== 0 && line[s] === line[s + 1] && line[s + 1] === line[s + 2]) {
                        bad = true; break;
                    }
                }
                // Walls touching idx.
                if (!bad && idx > 0) {
                    const w = wallsOnLine[idx - 1];
                    if (w != null && line[idx - 1] !== 0) {
                        if (w === 'same' && line[idx - 1] !== v) bad = true;
                        if (w === 'diff' && line[idx - 1] === v) bad = true;
                    }
                }
                if (!bad && idx < N - 1) {
                    const w = wallsOnLine[idx];
                    if (w != null && line[idx + 1] !== 0) {
                        if (w === 'same' && line[idx + 1] !== v) bad = true;
                        if (w === 'diff' && line[idx + 1] === v) bad = true;
                    }
                }
                if (!bad) {
                    if (ok(k + 1, curSun + (v === SUN ? 1 : 0),
                              curMoon + (v === MOON ? 1 : 0))) {
                        line[idx] = 0;
                        return true;
                    }
                }
                line[idx] = 0;
            }
            return false;
        }
        return ok(0, cs, cm);
    }

    /**
     * Is the empty cell (r, c) L3-forced by either its row or its
     * column? Returns SUN/MOON/0.
     *
     * Precondition: filled[r][c] === 0.
     */
    function l3ForcedAt(r, c, filled, wallIndex, N) {
        const forces = (orientation, lineIdx, posInLine) => {
            const line = extractLine(orientation, lineIdx, filled, N);
            const walls = lineWalls(orientation, lineIdx, wallIndex, N);
            const valids = [];
            for (const v of [SUN, MOON]) {
                line[posInLine] = v;
                if (canCompleteLine(line, walls, N)) valids.push(v);
                line[posInLine] = 0;
                if (valids.length === 2) return 0;
            }
            return valids.length === 1 ? valids[0] : 0;
        };
        return forces('row', r, c) || forces('col', c, r);
    }

    /**
     * Enumerate cells that are L3-forced (and not already L1-forced —
     * we want this list to be the "L3 only" upgrade over L1's coverage).
     */
    function findL3ErasableCells(filled, wallIndex, N) {
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = filled[r][c];
                if (v === 0) continue;
                filled[r][c] = 0;
                const l1 = l1ForcedAt(r, c, filled, wallIndex, N);
                if (l1 !== v) {
                    // L1 wouldn't cover this; check L3.
                    const l3 = l3ForcedAt(r, c, filled, wallIndex, N);
                    if (l3 === v) out.push([r, c]);
                }
                filled[r][c] = v;
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
    // Self-check: simulate the player applying the allowed tactics
    // until convergence and verify it reaches the solution. If this
    // ever fails the generator has a bug for that difficulty.
    //
    // `tactics` is an array such as ['L1'] or ['L1', 'L3'] — the
    // generator's contract for that difficulty.
    // -----------------------------------------------------------------

    function verifySolvable(prefilled, walls, solution, N, tactics) {
        const useL3 = tactics.includes('L3');
        const filled = prefilled.map((row) => row.slice());
        const wallIndex = buildWallIndex(walls);
        let progressed = true;
        while (progressed) {
            progressed = false;
            // Always try L1 first — cheap, catches the easy wins.
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
            if (progressed || !useL3) continue;
            // L1 stalled. Try one pass of L3.
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (filled[r][c] !== 0) continue;
                    const v = l3ForcedAt(r, c, filled, wallIndex, N);
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
    // Difficulty tunables.
    //
    //   tactics    : which tactic tiers the puzzle is allowed to need.
    //                Easy  = L1 only — feels obvious all the way.
    //                M / H = L1 + L3 — needs row/col-scoped lookaheads.
    //   wallBudget : how many seed walls to scatter compatibly with the
    //                solution before the main erase loop. Smaller = the
    //                puzzle leans harder on prefill / mid-loop walls.
    //
    // Medium and Hard share the tactic set; Hard differs in giving the
    // erase loop less wall scaffolding, which biases toward fewer
    // prefills + more L3 leverage in the solving sequence.
    // -----------------------------------------------------------------

    function difficultyParams(N, difficulty) {
        const base = Math.max(1, Math.floor(N / 3));
        if (difficulty === 'easy') {
            return { tactics: ['L1'], wallBudget: base + 1, preferL3: false };
        }
        if (difficulty === 'hard') {
            // Prefer L3-only erasures whenever they exist so the puzzle
            // has more cells that actually require L3 to solve. L3-only
            // candidates are scanned first; we fall back to L1 only when
            // L3 has nothing to offer (which is the early-game state
            // when the board is still dense).
            return {
                tactics: ['L1', 'L3'],
                wallBudget: Math.max(0, base - 1),
                preferL3: true,
            };
        }
        return {
            tactics: ['L1', 'L3'],
            wallBudget: base,
            preferL3: false,
        };
    }

    // -----------------------------------------------------------------
    // Main entry point.
    //
    // For Medium / Hard we don't trust a single attempt — the generator
    // is greedy and the L3-only erasures it picks can later be diluted
    // by L1 erasures that make those same cells L1-reachable from the
    // final prefill. So we run the inner constructor a handful of times
    // and pick the candidate with the highest "L3-required" count
    // (cells L1 alone cannot finish from prefill). Easy uses a single
    // attempt — its tactic budget excludes L3 anyway.
    // -----------------------------------------------------------------

    function generate(size, difficulty, seed) {
        const params = difficultyParams(size, difficulty);
        const wantsL3 = params.tactics.includes('L3');
        const target = wantsL3 ? 1 : 0;
        // Budget tuned from observed per-size yield in the stats page:
        // 6×6 Hard hits target ~7% of seeds, so 30 attempts give ~88%
        // coverage; larger boards converge in 1–3 attempts.
        const maxAttempts = wantsL3 ? 30 : 1;

        let best = null;
        let attemptsUsed = 0;
        for (let a = 0; a < maxAttempts; a++) {
            attemptsUsed = a + 1;
            const attemptSeed = (seed + a * 0x9e3779b9) >>> 0;
            const cand = generateOnce(size, difficulty, attemptSeed);
            if (!best || cand.stats.l3RequiredCells > best.stats.l3RequiredCells) {
                best = cand;
            }
            if (best.stats.l3RequiredCells >= target) break;
        }
        best.stats.attemptsUsed = attemptsUsed;
        return best;
    }

    function generateOnce(size, difficulty, seed) {
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
        const useL3 = params.tactics.includes('L3');
        const filled = solution.map((row) => row.slice());
        const walls = seedWalls(solution, rng, params.wallBudget, N);
        let wallIndex = buildWallIndex(walls);

        // Per-puzzle stats so we can see, after the fact, how much each
        // tactic tier actually got used. Surfaced in the puzzle output
        // so the stats / debug pages can read it without rerunning.
        const stats = { l1Erases: 0, l3Erases: 0, wallAdds: 0 };

        const maxIters = N * N * 4;
        for (let iter = 0; iter < maxIters; iter++) {
            // Tactic preference depends on difficulty:
            //   - Easy / Medium : L1 first, fall to L3 only if L1 stalls.
            //   - Hard          : prefer L3-only when available so the
            //                     puzzle leans on the harder tactic.
            // L1-only erasures and L3-only erasures are disjoint
            // (findL3ErasableCells filters out cells L1 already covers).
            let pick = null;
            let pickKind = null;
            if (useL3 && params.preferL3) {
                const l3 = findL3ErasableCells(filled, wallIndex, N);
                if (l3.length > 0) { pick = l3; pickKind = 'l3'; }
            }
            if (!pick) {
                const l1 = findL1ErasableCells(filled, wallIndex, N);
                if (l1.length > 0) { pick = l1; pickKind = 'l1'; }
            }
            if (!pick && useL3 && !params.preferL3) {
                const l3 = findL3ErasableCells(filled, wallIndex, N);
                if (l3.length > 0) { pick = l3; pickKind = 'l3'; }
            }
            if (pick) {
                const [r, c] = pick[Math.floor(rng() * pick.length)];
                filled[r][c] = 0;
                if (pickKind === 'l3') stats.l3Erases++;
                else stats.l1Erases++;
                continue;
            }
            const wallChoices =
                findWallAddCandidates(filled, walls, wallIndex, solution, N);
            if (wallChoices.length > 0) {
                const choice = wallChoices[Math.floor(rng() * wallChoices.length)];
                walls.push(choice.wall);
                stats.wallAdds++;
                // Rebuild rather than incrementally patch — the cost is
                // tiny and it keeps the index invariant trivially.
                wallIndex = buildWallIndex(walls);
                const [r, c] = choice.erasable[Math.floor(rng() * choice.erasable.length)];
                filled[r][c] = 0;
                stats.l1Erases++;
                continue;
            }
            break;
        }

        const prefillCount = filled.reduce(
            (a, row) => a + row.reduce((s, v) => s + (v ? 1 : 0), 0), 0);

        // How many cells does L1 alone leave unsolved? A non-zero count
        // means the player *must* invoke L3 (no L1-only path reaches the
        // solution from prefill). This is the strict "L3-required" metric
        // — distinct from "L3 was used during generation", which only
        // promises a single L3-using solve path exists.
        const l1OnlyFinal = (() => {
            const f = filled.map((row) => row.slice());
            const idx = buildWallIndex(walls);
            let progressed = true;
            while (progressed) {
                progressed = false;
                for (let r = 0; r < N; r++) {
                    for (let c = 0; c < N; c++) {
                        if (f[r][c] !== 0) continue;
                        const v = l1ForcedAt(r, c, f, idx, N);
                        if (v !== 0) { f[r][c] = v; progressed = true; }
                    }
                }
            }
            let empty = 0;
            for (const row of f) for (const v of row) if (v === 0) empty++;
            return empty;
        })();

        const puzzle = {
            id: `tango-${N}x${N}-${difficulty}-${seed.toString(36)}`,
            game: 'tango',
            size: N,
            difficulty,
            prefilled: filled,
            walls,
            solution,
            stats: {
                ...stats,
                prefillCount,
                wallCount: walls.length,
                l3RequiredCells: l1OnlyFinal,
            },
        };
        if (!verifySolvable(filled, walls, solution, N, params.tactics)) {
            // Dump enough to reproduce: the seed alone is sufficient
            // since generate(N, difficulty, seed) is deterministic.
            console.warn('[tango-gen] self-check failed for', puzzle.id,
                'tactics=' + params.tactics.join('+'),
                'seed=' + seed,
                'prefill=' + prefillCount,
                'walls=' + walls.length,
                'erases=L1:' + stats.l1Erases + '/L3:' + stats.l3Erases,
                'wallAdds=' + stats.wallAdds);
        }
        return puzzle;
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.tango = generate;
})(window);
