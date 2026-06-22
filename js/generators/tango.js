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
    // l1Explain returns { value, reason } when (r, c) is forced, else
    // null. l1ForcedAt is the fast-path wrapper that just returns the
    // value (or 0).
    //
    // Reason shapes — kept simple and machine-readable so the solver
    // trace UI can format them into natural language without parsing.
    //
    //   T-count : the line already has N/2 of one symbol.
    //             { kind: 'T-count', orientation: 'row'|'col',
    //               line: index, fullValue: SUN|MOON, value: opposite }
    //
    //   T-three : two adjacent (or one-over) cells along the line are
    //             the same symbol, so this cell must be the opposite.
    //             { kind: 'T-three', orientation: 'row'|'col',
    //               pattern: 'left'|'sandwich'|'right',
    //               sources: [[r1, c1], [r2, c2]],
    //               sourceValue: SUN|MOON, value: opposite }
    //
    //   T-wall  : a `=` / `×` wall pins this cell to a filled neighbour.
    //             { kind: 'T-wall', wallKind: 'same'|'diff',
    //               neighbor: [r', c'], neighborValue: SUN|MOON,
    //               value: derived }
    //
    // Precondition: filled[r][c] === 0.
    // -----------------------------------------------------------------

    function l1Explain(r, c, filled, wallIndex, N) {
        const half = N / 2;

        // T-count along the row.
        let rs = 0, rm = 0;
        for (let j = 0; j < N; j++) {
            if (filled[r][j] === SUN) rs++;
            else if (filled[r][j] === MOON) rm++;
        }
        if (rs >= half) {
            return { value: MOON, reason: { kind: 'T-count', orientation: 'row',
                line: r, fullValue: SUN, value: MOON } };
        }
        if (rm >= half) {
            return { value: SUN, reason: { kind: 'T-count', orientation: 'row',
                line: r, fullValue: MOON, value: SUN } };
        }

        // T-count along the column.
        let cs = 0, cm = 0;
        for (let i = 0; i < N; i++) {
            if (filled[i][c] === SUN) cs++;
            else if (filled[i][c] === MOON) cm++;
        }
        if (cs >= half) {
            return { value: MOON, reason: { kind: 'T-count', orientation: 'col',
                line: c, fullValue: SUN, value: MOON } };
        }
        if (cm >= half) {
            return { value: SUN, reason: { kind: 'T-count', orientation: 'col',
                line: c, fullValue: MOON, value: SUN } };
        }

        // T-three horizontally. Three patterns:
        //   [c-2][c-1][_]   two-same to the left
        //   [c-1][_][c+1]   sandwich (two-same straddling this cell)
        //   [_][c+1][c+2]   two-same to the right
        if (c >= 2) {
            const a = filled[r][c - 1], b = filled[r][c - 2];
            if (a !== 0 && a === b) {
                const value = a === SUN ? MOON : SUN;
                return { value, reason: { kind: 'T-three', orientation: 'row',
                    pattern: 'left', sources: [[r, c - 2], [r, c - 1]],
                    sourceValue: a, value } };
            }
        }
        if (c >= 1 && c + 1 < N) {
            const a = filled[r][c - 1], b = filled[r][c + 1];
            if (a !== 0 && a === b) {
                const value = a === SUN ? MOON : SUN;
                return { value, reason: { kind: 'T-three', orientation: 'row',
                    pattern: 'sandwich', sources: [[r, c - 1], [r, c + 1]],
                    sourceValue: a, value } };
            }
        }
        if (c + 2 < N) {
            const a = filled[r][c + 1], b = filled[r][c + 2];
            if (a !== 0 && a === b) {
                const value = a === SUN ? MOON : SUN;
                return { value, reason: { kind: 'T-three', orientation: 'row',
                    pattern: 'right', sources: [[r, c + 1], [r, c + 2]],
                    sourceValue: a, value } };
            }
        }

        // T-three vertically (same shape).
        if (r >= 2) {
            const a = filled[r - 1][c], b = filled[r - 2][c];
            if (a !== 0 && a === b) {
                const value = a === SUN ? MOON : SUN;
                return { value, reason: { kind: 'T-three', orientation: 'col',
                    pattern: 'left', sources: [[r - 2, c], [r - 1, c]],
                    sourceValue: a, value } };
            }
        }
        if (r >= 1 && r + 1 < N) {
            const a = filled[r - 1][c], b = filled[r + 1][c];
            if (a !== 0 && a === b) {
                const value = a === SUN ? MOON : SUN;
                return { value, reason: { kind: 'T-three', orientation: 'col',
                    pattern: 'sandwich', sources: [[r - 1, c], [r + 1, c]],
                    sourceValue: a, value } };
            }
        }
        if (r + 2 < N) {
            const a = filled[r + 1][c], b = filled[r + 2][c];
            if (a !== 0 && a === b) {
                const value = a === SUN ? MOON : SUN;
                return { value, reason: { kind: 'T-three', orientation: 'col',
                    pattern: 'right', sources: [[r + 1, c], [r + 2, c]],
                    sourceValue: a, value } };
            }
        }

        // T-wall: a `=` / `×` wall to a known neighbour.
        const adj = wallIndex.byCell.get(cellKey(r, c));
        if (adj) {
            for (const { kind, otherR, otherC } of adj) {
                const v = filled[otherR][otherC];
                if (v === 0) continue;
                const value = kind === 'same' ? v : (v === SUN ? MOON : SUN);
                return { value, reason: { kind: 'T-wall', wallKind: kind,
                    neighbor: [otherR, otherC], neighborValue: v, value } };
            }
        }
        return null;
    }

    function l1ForcedAt(r, c, filled, wallIndex, N) {
        const e = l1Explain(r, c, filled, wallIndex, N);
        return e ? e.value : 0;
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
    // Contradiction detection
    //
    // Given a filled board and a wall index, is anything illegal? Used
    // by L2's forward propagation to spot the moment a hypothetical
    // chain self-destructs.
    //
    // findContradictionAt(r, c, ...) only checks the constraints that
    // involve cell (r, c) — cheap O(N) per call, perfect for
    // incremental checks after placing one cell.
    //
    // Returned shape:
    //   { kind: 'count-overflow', orientation, line, value, count }
    //   { kind: 'three-in-row',  orientation, cells: [[r,c]×3], value }
    //   { kind: 'wall',          wallKind, cells: [[r,c],[r',c']], values: [v, v'] }
    // -----------------------------------------------------------------

    function findContradictionAt(r, c, filled, wallIndex, N, predicate) {
        const accept = predicate || (() => true);
        const half = N / 2;
        const v = filled[r][c];
        if (v === 0) return null;

        // Count overflow in row r and col c.
        let rs = 0, rm = 0;
        for (let j = 0; j < N; j++) {
            if (filled[r][j] === SUN) rs++;
            else if (filled[r][j] === MOON) rm++;
        }
        if (rs > half) {
            const cd = { kind: 'count-overflow', orientation: 'row', line: r, value: SUN, count: rs };
            if (accept(cd)) return cd;
        }
        if (rm > half) {
            const cd = { kind: 'count-overflow', orientation: 'row', line: r, value: MOON, count: rm };
            if (accept(cd)) return cd;
        }
        let cs = 0, cm = 0;
        for (let i = 0; i < N; i++) {
            if (filled[i][c] === SUN) cs++;
            else if (filled[i][c] === MOON) cm++;
        }
        if (cs > half) {
            const cd = { kind: 'count-overflow', orientation: 'col', line: c, value: SUN, count: cs };
            if (accept(cd)) return cd;
        }
        if (cm > half) {
            const cd = { kind: 'count-overflow', orientation: 'col', line: c, value: MOON, count: cm };
            if (accept(cd)) return cd;
        }

        // Three-in-a-row windows containing (r, c).
        for (let s = Math.max(0, c - 2); s <= Math.min(c, N - 3); s++) {
            if (filled[r][s] === v && filled[r][s + 1] === v && filled[r][s + 2] === v) {
                const cd = { kind: 'three-in-row', orientation: 'row',
                    cells: [[r, s], [r, s + 1], [r, s + 2]], value: v };
                if (accept(cd)) return cd;
            }
        }
        for (let s = Math.max(0, r - 2); s <= Math.min(r, N - 3); s++) {
            if (filled[s][c] === v && filled[s + 1][c] === v && filled[s + 2][c] === v) {
                const cd = { kind: 'three-in-row', orientation: 'col',
                    cells: [[s, c], [s + 1, c], [s + 2, c]], value: v };
                if (accept(cd)) return cd;
            }
        }

        // Wall violations touching (r, c).
        const adj = wallIndex.byCell.get(cellKey(r, c));
        if (adj) {
            for (const { kind, otherR, otherC } of adj) {
                const ov = filled[otherR][otherC];
                if (ov === 0) continue;
                if (kind === 'same' && v !== ov) {
                    const cd = { kind: 'wall', wallKind: 'same',
                        cells: [[r, c], [otherR, otherC]], values: [v, ov] };
                    if (accept(cd)) return cd;
                }
                if (kind === 'diff' && v === ov) {
                    const cd = { kind: 'wall', wallKind: 'diff',
                        cells: [[r, c], [otherR, otherC]], values: [v, ov] };
                    if (accept(cd)) return cd;
                }
            }
        }
        return null;
    }

    // -----------------------------------------------------------------
    // L2 / L3 / L4 deductions — hypothesize + L1 fixpoint, with three
    // distinct difficulty bands. The cost graph is:
    //
    //   L2 (line, 1 step)
    //     Hypothesise X = v at (r, c). Propagate L1 only within row r
    //     ∪ col c. If the VERY FIRST L1 placement triggers an in-line
    //     contradiction, X is forced. Cognitively about as cheap as L1:
    //     "if I try this here, the cell next to it would have to be the
    //     same thing and that breaks a wall / three-in-a-row".
    //
    //   L3 (line, ≥2 steps)
    //     Same line-bounded propagation, but the contradiction only
    //     appears after a chain of 2+ L1 placements. The player has to
    //     hold a sequence in their head while staring at one row/column.
    //
    //   L4 (line + 1 perpendicular layer)
    //     Hypothesise on (r, c). Run line-bounded propagation on row r
    //     ∪ col c just like L3 — but every time we place a cell on the
    //     primary line, we ALSO unlock its perpendicular line for
    //     propagation. Placements on those unlocked perpendiculars
    //     don't chain further. Contradictions must live in the
    //     unlocked scope. Player experience: "this row fills out and
    //     now I can see one of its columns has a problem".
    //
    // L2 ⊆ L3 ⊆ L4 in *coverage* (L2 cases would also fire under L3 or
    // L4 logic). We classify cells by the SMALLEST tier that forces
    // them so the difficulty buckets stay disjoint.
    //
    // The two scopes (line-bounded / anywhere) share
    // runHypothesisPropagation; the `inScope` / `contradictionInScope`
    // predicates control what counts.
    //
    // Reason shape:
    //   { kind: 'L2'|'L3'|'L4',
    //     hypothesis: { cell: [r, c], value: triedValue },
    //     propagation: [{ cell, value, reason: <L1 reason> }, ...],
    //     contradiction: <see findContradictionAt>,
    //     value }
    // -----------------------------------------------------------------

    /**
     * Hypothesise X = v at (r, c), propagate L1 through the cells the
     * `inScope(rr, cc)` predicate accepts, and report any contradiction
     * also accepted by `contradictionInScope(contradict)`.
     *
     * Returns { triedValue, propagation, contradiction } on success, or
     * null when no value leads to an in-scope contradiction.
     */
    function runHypothesisPropagation(r, c, filled, wallIndex, N, inScope, contradictionInScope) {
        for (const tryV of [SUN, MOON]) {
            const f = filled.map((row) => row.slice());
            f[r][c] = tryV;

            // Immediate contradiction at the hypothesised cell — that's
            // really an L1 refutation; leave it to L1.
            const direct = findContradictionAt(r, c, f, wallIndex, N);
            if (direct) continue;

            const trace = [];
            let contradict = null;
            let progressed = true;
            while (progressed && !contradict) {
                progressed = false;
                for (let rr = 0; rr < N && !contradict; rr++) {
                    for (let cc = 0; cc < N && !contradict; cc++) {
                        if (f[rr][cc] !== 0) continue;
                        if (!inScope(rr, cc)) continue;
                        const e = l1Explain(rr, cc, f, wallIndex, N);
                        if (!e) continue;
                        f[rr][cc] = e.value;
                        trace.push({ cell: [rr, cc], value: e.value, reason: e.reason });
                        progressed = true;
                        const c2 = findContradictionAt(rr, cc, f, wallIndex, N, contradictionInScope);
                        if (c2) contradict = c2;
                    }
                }
            }

            if (contradict) {
                return { triedValue: tryV, propagation: trace, contradiction: contradict };
            }
        }
        return null;
    }

    /**
     * Run *single-line* hypothesis propagation along one orientation
     * ('row' uses row r as the only line; 'col' uses col c).
     * Placements and contradictions are both clamped to that single
     * line. Returns null if the orientation doesn't refute either
     * value of (r, c).
     *
     * Player model: focus on EITHER the row OR the column the cell is
     * on, never both at once. L2/L3 try row first, then column, and
     * report whichever fires.
     */
    function singleLineHypothesisExplain(r, c, filled, wallIndex, N, orientation) {
        const isRow = orientation === 'row';
        const inScope = isRow
            ? (rr) => rr === r
            : (_, cc) => cc === c;
        const lineMatch = (cd) =>
            isRow
                ? cd.orientation === 'row' && cd.line === r
                : cd.orientation === 'col' && cd.line === c;
        const contradictionInScope = (cd) => {
            if (cd.kind === 'count-overflow') return lineMatch(cd);
            if (cd.kind === 'three-in-row') {
                // All three cells live on the same line; check the line index.
                if (cd.orientation === 'row') return isRow && cd.cells[0][0] === r;
                return !isRow && cd.cells[0][1] === c;
            }
            // wall: both ends must be on the chosen line.
            return cd.cells.every(([rr, cc]) => inScope(rr, cc));
        };
        const result = runHypothesisPropagation(r, c, filled, wallIndex, N,
            inScope, contradictionInScope);
        if (!result) return null;
        const value = result.triedValue === SUN ? MOON : SUN;
        return {
            value,
            triedValue: result.triedValue,
            chainLength: result.propagation.length,
            propagation: result.propagation,
            contradiction: result.contradiction,
            orientation,
        };
    }

    function l2Explain(r, c, filled, wallIndex, N) {
        // L2 = single-line propagation, EXACTLY 1 L1 placement before
        // an in-line contradiction. Try row first, then column.
        for (const orient of ['row', 'col']) {
            const e = singleLineHypothesisExplain(r, c, filled, wallIndex, N, orient);
            if (e && e.chainLength === 1) {
                return {
                    value: e.value,
                    reason: {
                        kind: 'L2',
                        hypothesis: { cell: [r, c], value: e.triedValue },
                        propagation: e.propagation,
                        contradiction: e.contradiction,
                        orientation: e.orientation,
                        value: e.value,
                    },
                };
            }
        }
        return null;
    }

    function l3Explain(r, c, filled, wallIndex, N) {
        // L3 = single-line propagation, chain of ≥2 L1 placements
        // before the in-line contradiction. Try row first, then column.
        for (const orient of ['row', 'col']) {
            const e = singleLineHypothesisExplain(r, c, filled, wallIndex, N, orient);
            if (e && e.chainLength >= 2) {
                return {
                    value: e.value,
                    reason: {
                        kind: 'L3',
                        hypothesis: { cell: [r, c], value: e.triedValue },
                        propagation: e.propagation,
                        contradiction: e.contradiction,
                        orientation: e.orientation,
                        value: e.value,
                    },
                };
            }
        }
        return null;
    }

    /**
     * L4 = "single primary line + ONE independent perp line".
     *
     * Pick row r OR col c as primary. Propagate L1 along that single
     * primary line to completion (no contradiction needed there — if
     * the primary line itself contradicts, that's L3, not L4).
     *
     * Then, for each perpendicular line opened by a primary-line
     * placement (including the hypothesis cell's own perpendicular):
     *   - snapshot the post-primary board state,
     *   - propagate L1 *only* along that single perpendicular line,
     *   - if a contradiction inside (primary ∪ perp) shows up, L4 fires.
     *
     * Each perpendicular line is checked INDEPENDENTLY of the others:
     * L1 placements in one perpendicular never feed into another
     * perpendicular's deduction. That keeps the player's mental model
     * honest — they only ever chase one perp at a time.
     *
     * L4 = (row variant fires) OR (col variant fires).
     */
    function l4Explain(r, c, filled, wallIndex, N) {
        for (const orient of ['row', 'col']) {
            const out = singleLineWithPerpExtension(r, c, filled, wallIndex, N, orient);
            if (out) return out;
        }
        return null;
    }

    function singleLineWithPerpExtension(r, c, filled, wallIndex, N, orientation) {
        const isRow = orientation === 'row';

        for (const tryV of [SUN, MOON]) {
            const f = filled.map((row) => row.slice());
            f[r][c] = tryV;
            if (findContradictionAt(r, c, f, wallIndex, N)) continue;  // L1 territory

            // ----- Primary phase: propagate L1 along the single primary line. -----
            const primary = runPrimaryLinePropagation(r, c, f, wallIndex, N, orientation);
            // f is now mutated with the primary-line placements.
            if (primary.contradiction) {
                // Primary alone contradicts ⇒ this is L3 territory, not L4.
                continue;
            }

            // ----- Collect candidate perp indices. -----
            //   Hypothesis itself counts as a primary-line placement, so its
            //   perpendicular line is open from the start.
            const perpIndices = new Set();
            if (isRow) {
                perpIndices.add(c);
                for (const p of primary.trace) perpIndices.add(p.cell[1]);
            } else {
                perpIndices.add(r);
                for (const p of primary.trace) perpIndices.add(p.cell[0]);
            }

            // ----- Perp phase: check each perp INDEPENDENTLY. -----
            for (const perpIdx of Array.from(perpIndices).sort((a, b) => a - b)) {
                const perp = runPerpLineCheck(r, c, f, wallIndex, N, orientation, perpIdx);
                if (!perp.contradiction) continue;
                const value = tryV === SUN ? MOON : SUN;
                return {
                    value,
                    reason: {
                        kind: 'L4',
                        hypothesis: { cell: [r, c], value: tryV },
                        orientation,
                        primaryPropagation: primary.trace,
                        perpOrientation: isRow ? 'col' : 'row',
                        perpIndex: perpIdx,
                        perpPropagation: perp.trace,
                        contradiction: perp.contradiction,
                        // Convenience: combined propagation for any caller that
                        // only wants a flat list (e.g. step counters, board
                        // highlights).
                        propagation: primary.trace.concat(perp.trace),
                        value,
                    },
                };
            }
        }
        return null;
    }

    /**
     * Propagate L1 along a single primary line (row r if isRow else col c).
     * Mutates `f` in place. Returns { trace, contradiction } where the
     * contradiction (if any) is restricted to the primary line's own
     * cells/constraints — out-of-line side effects are left for the perp
     * phase to discover.
     */
    function runPrimaryLinePropagation(r, c, f, wallIndex, N, orientation) {
        const isRow = orientation === 'row';
        const inScope = isRow
            ? (rr) => rr === r
            : (_, cc) => cc === c;
        const lineMatch = (cd) =>
            isRow
                ? cd.orientation === 'row' && cd.line === r
                : cd.orientation === 'col' && cd.line === c;
        const contradictionInScope = (cd) => {
            if (cd.kind === 'count-overflow') return lineMatch(cd);
            if (cd.kind === 'three-in-row') {
                if (cd.orientation === 'row') return isRow && cd.cells[0][0] === r;
                return !isRow && cd.cells[0][1] === c;
            }
            return cd.cells.every(([rr, cc]) => inScope(rr, cc));
        };
        const trace = [];
        let contradict = null;
        let progressed = true;
        while (progressed && !contradict) {
            progressed = false;
            if (isRow) {
                for (let cc = 0; cc < N && !contradict; cc++) {
                    if (f[r][cc] !== 0) continue;
                    const e = l1Explain(r, cc, f, wallIndex, N);
                    if (!e) continue;
                    f[r][cc] = e.value;
                    trace.push({ cell: [r, cc], value: e.value, reason: e.reason });
                    progressed = true;
                    const c2 = findContradictionAt(r, cc, f, wallIndex, N, contradictionInScope);
                    if (c2) contradict = c2;
                }
            } else {
                for (let rr = 0; rr < N && !contradict; rr++) {
                    if (f[rr][c] !== 0) continue;
                    const e = l1Explain(rr, c, f, wallIndex, N);
                    if (!e) continue;
                    f[rr][c] = e.value;
                    trace.push({ cell: [rr, c], value: e.value, reason: e.reason });
                    progressed = true;
                    const c2 = findContradictionAt(rr, c, f, wallIndex, N, contradictionInScope);
                    if (c2) contradict = c2;
                }
            }
        }
        return { trace, contradiction: contradict };
    }

    /**
     * Independently check one perpendicular line: snapshot the post-primary
     * board, propagate L1 ONLY along that perp line, and accept any
     * contradiction whose cells all live in (primary ∪ perp). The caller's
     * board state is NOT mutated.
     */
    function runPerpLineCheck(r, c, baseF, wallIndex, N, primaryOrientation, perpIdx) {
        const isRow = primaryOrientation === 'row';
        const f = baseF.map((row) => row.slice());

        // primary ∪ perp scope predicate.
        const inScope = (rr, cc) =>
            isRow
                ? (rr === r || cc === perpIdx)
                : (cc === c || rr === perpIdx);
        const contradictionInScope = (cd) => {
            if (cd.kind === 'count-overflow') {
                if (isRow) {
                    return (cd.orientation === 'row' && cd.line === r)
                        || (cd.orientation === 'col' && cd.line === perpIdx);
                }
                return (cd.orientation === 'col' && cd.line === c)
                    || (cd.orientation === 'row' && cd.line === perpIdx);
            }
            return cd.cells.every(([rr, cc]) => inScope(rr, cc));
        };

        const trace = [];
        let contradict = null;

        // Initial sweep: primary placements may already have created
        // contradictions that touch the perp line (e.g. a wall whose other
        // end sits on the perp line). Catch those before doing any new L1.
        if (isRow) {
            for (let rr = 0; rr < N && !contradict; rr++) {
                if (f[rr][perpIdx] === 0) continue;
                const c2 = findContradictionAt(rr, perpIdx, f, wallIndex, N, contradictionInScope);
                if (c2) contradict = c2;
            }
        } else {
            for (let cc = 0; cc < N && !contradict; cc++) {
                if (f[perpIdx][cc] === 0) continue;
                const c2 = findContradictionAt(perpIdx, cc, f, wallIndex, N, contradictionInScope);
                if (c2) contradict = c2;
            }
        }

        // L1 propagation restricted to the perp line.
        let progressed = true;
        while (progressed && !contradict) {
            progressed = false;
            if (isRow) {
                for (let rr = 0; rr < N && !contradict; rr++) {
                    if (f[rr][perpIdx] !== 0) continue;
                    const e = l1Explain(rr, perpIdx, f, wallIndex, N);
                    if (!e) continue;
                    f[rr][perpIdx] = e.value;
                    trace.push({ cell: [rr, perpIdx], value: e.value, reason: e.reason });
                    progressed = true;
                    const c2 = findContradictionAt(rr, perpIdx, f, wallIndex, N, contradictionInScope);
                    if (c2) contradict = c2;
                }
            } else {
                for (let cc = 0; cc < N && !contradict; cc++) {
                    if (f[perpIdx][cc] !== 0) continue;
                    const e = l1Explain(perpIdx, cc, f, wallIndex, N);
                    if (!e) continue;
                    f[perpIdx][cc] = e.value;
                    trace.push({ cell: [perpIdx, cc], value: e.value, reason: e.reason });
                    progressed = true;
                    const c2 = findContradictionAt(perpIdx, cc, f, wallIndex, N, contradictionInScope);
                    if (c2) contradict = c2;
                }
            }
        }

        return { trace, contradiction: contradict };
    }

    function l2ForcedAt(r, c, filled, wallIndex, N) {
        const e = l2Explain(r, c, filled, wallIndex, N);
        return e ? e.value : 0;
    }
    function l3ForcedAt(r, c, filled, wallIndex, N) {
        const e = l3Explain(r, c, filled, wallIndex, N);
        return e ? e.value : 0;
    }
    function l4ForcedAt(r, c, filled, wallIndex, N) {
        const e = l4Explain(r, c, filled, wallIndex, N);
        return e ? e.value : 0;
    }

    /**
     * Disjoint erasable-cell sets per tier. Each `findL{K}ErasableCells`
     * returns cells uniquely first-classified at that tier (i.e. no
     * lower tier forces the same cell). This makes the generator's tier
     * preference free of double counting.
     */
    function findL2ErasableCells(filled, wallIndex, N) {
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = filled[r][c];
                if (v === 0) continue;
                filled[r][c] = 0;
                if (l1ForcedAt(r, c, filled, wallIndex, N) !== v
                    && l2ForcedAt(r, c, filled, wallIndex, N) === v) {
                    out.push([r, c]);
                }
                filled[r][c] = v;
            }
        }
        return out;
    }

    function findL3ErasableCells(filled, wallIndex, N) {
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = filled[r][c];
                if (v === 0) continue;
                filled[r][c] = 0;
                if (l1ForcedAt(r, c, filled, wallIndex, N) !== v
                    && l2ForcedAt(r, c, filled, wallIndex, N) !== v
                    && l3ForcedAt(r, c, filled, wallIndex, N) === v) {
                    out.push([r, c]);
                }
                filled[r][c] = v;
            }
        }
        return out;
    }

    function findL4ErasableCells(filled, wallIndex, N) {
        const out = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = filled[r][c];
                if (v === 0) continue;
                filled[r][c] = 0;
                if (l1ForcedAt(r, c, filled, wallIndex, N) !== v
                    && l2ForcedAt(r, c, filled, wallIndex, N) !== v
                    && l3ForcedAt(r, c, filled, wallIndex, N) !== v
                    && l4ForcedAt(r, c, filled, wallIndex, N) === v) {
                    out.push([r, c]);
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
        const tierFn = {
            L1: l1ForcedAt,
            L2: l2ForcedAt,
            L3: l3ForcedAt,
            L4: l4ForcedAt,
        };
        const tierOrder = ['L1', 'L2', 'L3', 'L4']
            .filter((t) => tactics.includes(t));
        const filled = prefilled.map((row) => row.slice());
        const wallIndex = buildWallIndex(walls);

        // At each pass, try each allowed tier in increasing order.
        // As soon as some tier makes progress we restart from L1 — we
        // want easier tactics to mop up everything they can before we
        // pay for harder ones.
        let progressed = true;
        while (progressed) {
            progressed = false;
            for (const tier of tierOrder) {
                const fn = tierFn[tier];
                for (let r = 0; r < N; r++) {
                    for (let c = 0; c < N; c++) {
                        if (filled[r][c] !== 0) continue;
                        const v = fn(r, c, filled, wallIndex, N);
                        if (v !== 0) {
                            filled[r][c] = v;
                            progressed = true;
                        }
                    }
                }
                if (progressed) break;  // restart from L1 next iter
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
    //                Easy   = L1 + L2 — direct rules, plus one-step
    //                         line-bounded hypotheses (still feels L1-y).
    //                Medium = + L3      — multi-step line hypotheses.
    //                Hard   = + L4      — cross-board hypotheses.
    //   wallBudget : how many seed walls to scatter compatibly with the
    //                solution before the main erase loop. Smaller = the
    //                puzzle leans harder on prefill / mid-loop walls.
    //   preferHigh : during the erase loop, greedily pick the highest
    //                allowed tier whenever it has candidates. Pushes
    //                the puzzle toward actually needing the hardest
    //                tactic it's allowed to use.
    // -----------------------------------------------------------------

    function difficultyParams(N, difficulty) {
        const base = Math.max(1, Math.floor(N / 3));
        if (difficulty === 'easy') {
            return {
                tactics: ['L1', 'L2'],
                wallBudget: base + 1,
                preferHigh: false,
            };
        }
        if (difficulty === 'hard') {
            return {
                tactics: ['L1', 'L2', 'L3', 'L4'],
                wallBudget: Math.max(0, base - 1),
                preferHigh: true,
            };
        }
        // Medium
        return {
            tactics: ['L1', 'L2', 'L3'],
            wallBudget: base,
            preferHigh: true,
        };
    }

    // -----------------------------------------------------------------
    // Main entry point.
    //
    // For Medium / Hard we don't trust a single attempt — the generator
    // is greedy and the higher-tier erasures it picks can later be
    // diluted by lower-tier erasures that make those same cells reach-
    // able from the final prefill. So we run the inner constructor a
    // handful of times and pick the candidate with the highest count
    // of cells that *strictly require* the difficulty's headline tier
    // (L3 for Medium, L4 for Hard). Easy uses a single attempt.
    // -----------------------------------------------------------------

    function generate(size, difficulty, seed) {
        const params = difficultyParams(size, difficulty);
        // Pick the metric to maximise per difficulty:
        //   Hard   → strict L4-required (cells L1+L2+L3 can't reach)
        //   Medium → strict L3-required (cells L1+L2 can't reach)
        //   Easy   → no retry — its tactic budget is L1 + L2 only.
        const scoreOf = difficulty === 'hard'
            ? (p) => p.stats.l4RequiredCells
            : difficulty === 'medium'
                ? (p) => p.stats.l3OrAboveRequiredCells
                : (_) => 0;
        const wantsRetry = difficulty !== 'easy';
        const target = wantsRetry ? 1 : 0;
        const maxAttempts = wantsRetry ? 30 : 1;

        let best = null;
        let attemptsUsed = 0;
        for (let a = 0; a < maxAttempts; a++) {
            attemptsUsed = a + 1;
            const attemptSeed = (seed + a * 0x9e3779b9) >>> 0;
            const cand = generateOnce(size, difficulty, attemptSeed);
            if (!best || scoreOf(cand) > scoreOf(best)) best = cand;
            if (scoreOf(best) >= target) break;
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
        const useL2 = params.tactics.includes('L2');
        const useL3 = params.tactics.includes('L3');
        const useL4 = params.tactics.includes('L4');
        const filled = solution.map((row) => row.slice());
        const walls = seedWalls(solution, rng, params.wallBudget, N);
        let wallIndex = buildWallIndex(walls);

        // Per-puzzle stats so we can see, after the fact, how much each
        // tactic tier actually got used. Surfaced in the puzzle output
        // so the stats / debug pages can read it without rerunning.
        const stats = {
            l1Erases: 0, l2Erases: 0, l3Erases: 0, l4Erases: 0,
            wallAdds: 0,
        };

        const maxIters = N * N * 4;
        for (let iter = 0; iter < maxIters; iter++) {
            // Tier preference per difficulty:
            //   - Easy   : L1 first, L2 as bonus.
            //   - Medium : L3 → L2 → L1 (push toward needing L3).
            //   - Hard   : L4 → L3 → L2 → L1 (push toward needing L4).
            // findL{1..4}ErasableCells return disjoint sets, so the
            // tier ordering directly drives what kind of cell we erase.
            let pick = null;
            let pickKind = null;
            const tryAt = (tier, finder) => {
                if (pick) return;
                const l = finder(filled, wallIndex, N);
                if (l.length > 0) { pick = l; pickKind = tier; }
            };
            const tryL1 = () => tryAt('l1', findL1ErasableCells);
            const tryL2 = () => { if (useL2) tryAt('l2', findL2ErasableCells); };
            const tryL3 = () => { if (useL3) tryAt('l3', findL3ErasableCells); };
            const tryL4 = () => { if (useL4) tryAt('l4', findL4ErasableCells); };
            if (params.preferHigh) {
                tryL4(); tryL3(); tryL2(); tryL1();
            } else {
                tryL1(); tryL2(); tryL3(); tryL4();
            }
            if (pick) {
                const [r, c] = pick[Math.floor(rng() * pick.length)];
                filled[r][c] = 0;
                stats[pickKind + 'Erases']++;
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

        // Three "what does the player *have* to use" metrics by
        // running a tier-restricted fixpoint from prefill and counting
        // unsolved cells:
        //   l2OrAboveRequired : empty after L1 alone        (need ≥ L2)
        //   l3OrAboveRequired : empty after L1+L2           (need ≥ L3)
        //   l4Required        : empty after L1+L2+L3        (need L4)
        const tierFns = {
            L1: l1ForcedAt,
            L2: l2ForcedAt,
            L3: l3ForcedAt,
            L4: l4ForcedAt,
        };
        const runFixpoint = (tiers) => {
            const f = filled.map((row) => row.slice());
            const idx = buildWallIndex(walls);
            let progressed = true;
            while (progressed) {
                progressed = false;
                for (const tier of tiers) {
                    const fn = tierFns[tier];
                    for (let r = 0; r < N; r++) {
                        for (let c = 0; c < N; c++) {
                            if (f[r][c] !== 0) continue;
                            const v = fn(r, c, f, idx, N);
                            if (v !== 0) { f[r][c] = v; progressed = true; }
                        }
                    }
                    if (progressed) break;  // restart from lowest tier
                }
            }
            let empty = 0;
            for (const row of f) for (const v of row) if (v === 0) empty++;
            return empty;
        };
        const l2OrAboveRequired = runFixpoint(['L1']);
        const l3OrAboveRequired = runFixpoint(['L1', 'L2']);
        const l4Required = runFixpoint(['L1', 'L2', 'L3']);

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
                l2OrAboveRequiredCells: l2OrAboveRequired,
                l3OrAboveRequiredCells: l3OrAboveRequired,
                l4RequiredCells: l4Required,
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
                'erases=L1:' + stats.l1Erases + '/L2:' + stats.l2Erases
                    + '/L3:' + stats.l3Erases + '/L4:' + stats.l4Erases,
                'wallAdds=' + stats.wallAdds);
        }
        return puzzle;
    }

    // -----------------------------------------------------------------
    // Solver step — used by tooling that wants to step through a puzzle
    // deduction-by-deduction. Returns the next available step using the
    // lowest tier that fires, or null when no tactic forces anything.
    //
    // Output:
    //   { tier: 'L1'|'L2'|'L3', cell: [r, c], value, reason }
    //
    // The caller owns `filled` and is expected to apply the placement
    // (filled[r][c] = value) between calls. Walls are provided as a
    // wall array (same shape used in puzzle output).
    // -----------------------------------------------------------------

    function nextDeduction(filled, walls, N, tactics) {
        const wallIndex = buildWallIndex(walls);
        const allowed = tactics || ['L1', 'L2', 'L3', 'L4'];
        const tierExplain = {
            L1: l1Explain,
            L2: l2Explain,
            L3: l3Explain,
            L4: l4Explain,
        };
        for (const tier of ['L1', 'L2', 'L3', 'L4']) {
            if (!allowed.includes(tier)) continue;
            const fn = tierExplain[tier];
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (filled[r][c] !== 0) continue;
                    const e = fn(r, c, filled, wallIndex, N);
                    if (e) return { tier, cell: [r, c], value: e.value, reason: e.reason };
                }
            }
        }
        return null;
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.tango = generate;
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleSolvers.tango = {
        nextDeduction,
        SUN, MOON,
    };
})(window);
