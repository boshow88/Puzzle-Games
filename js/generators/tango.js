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
        const parent = new Map();
        const find = (k) => {
            let r = k;
            while (parent.get(r) !== r) r = parent.get(r);
            while (parent.get(k) !== r) {
                const nxt = parent.get(k);
                parent.set(k, r);
                k = nxt;
            }
            return r;
        };
        for (const w of walls) {
            seen.add(wallKey(w.r1, w.c1, w.r2, w.c2));
            const a = cellKey(w.r1, w.c1);
            const b = cellKey(w.r2, w.c2);
            if (!byCell.has(a)) byCell.set(a, []);
            if (!byCell.has(b)) byCell.set(b, []);
            byCell.get(a).push({ kind: w.kind, otherR: w.r2, otherC: w.c2 });
            byCell.get(b).push({ kind: w.kind, otherR: w.r1, otherC: w.c1 });
            if (!parent.has(a)) parent.set(a, a);
            if (!parent.has(b)) parent.set(b, b);
            const ra = find(a), rb = find(b);
            if (ra !== rb) parent.set(ra, rb);
        }
        // Connected component id for cell (r,c) over the puzzle wall graph.
        // Cells with no walls return their own cellKey (singleton component).
        const wallComponentOf = (r, c) => {
            const k = cellKey(r, c);
            if (!parent.has(k)) return k;
            return find(k);
        };
        return { byCell, seen, wallComponentOf };
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
    //               line: index, fullValue: SUN|MOON, value: opposite,
    //               sources: [[r1, c1], ...] }   // the N/2 same-color cells
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
    //               value: derived, sources: [[r', c']] }
    //
    // Every reason now carries `sources`, the list of cells whose
    // current values the rule depends on. Backward-closure code uses
    // this to compute minimum chain lengths.
    //
    // Precondition: filled[r][c] === 0.
    // -----------------------------------------------------------------

    function l1Explain(r, c, filled, wallIndex, N) {
        const half = N / 2;

        // T-count along the row.
        let rs = 0, rm = 0;
        const rsCells = [], rmCells = [];
        for (let j = 0; j < N; j++) {
            if (filled[r][j] === SUN) { rs++; rsCells.push([r, j]); }
            else if (filled[r][j] === MOON) { rm++; rmCells.push([r, j]); }
        }
        if (rs >= half) {
            return { value: MOON, reason: { kind: 'T-count', orientation: 'row',
                line: r, fullValue: SUN, value: MOON, sources: rsCells } };
        }
        if (rm >= half) {
            return { value: SUN, reason: { kind: 'T-count', orientation: 'row',
                line: r, fullValue: MOON, value: SUN, sources: rmCells } };
        }

        // T-count along the column.
        let cs = 0, cm = 0;
        const csCells = [], cmCells = [];
        for (let i = 0; i < N; i++) {
            if (filled[i][c] === SUN) { cs++; csCells.push([i, c]); }
            else if (filled[i][c] === MOON) { cm++; cmCells.push([i, c]); }
        }
        if (cs >= half) {
            return { value: MOON, reason: { kind: 'T-count', orientation: 'col',
                line: c, fullValue: SUN, value: MOON, sources: csCells } };
        }
        if (cm >= half) {
            return { value: SUN, reason: { kind: 'T-count', orientation: 'col',
                line: c, fullValue: MOON, value: SUN, sources: cmCells } };
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
                    neighbor: [otherR, otherC], neighborValue: v, value,
                    sources: [[otherR, otherC]] } };
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
    // Returned shape (every kind carries `cells` — the cells whose values
    // jointly demonstrate the violation; backward-closure walks them):
    //   { kind: 'count-overflow', orientation, line, value, count,
    //     cells: [[r,c], ...] }                  // all same-color cells on the line
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
        const rsCells = [], rmCells = [];
        for (let j = 0; j < N; j++) {
            if (filled[r][j] === SUN) { rs++; rsCells.push([r, j]); }
            else if (filled[r][j] === MOON) { rm++; rmCells.push([r, j]); }
        }
        if (rs > half) {
            const cd = { kind: 'count-overflow', orientation: 'row', line: r, value: SUN, count: rs, cells: rsCells };
            if (accept(cd)) return cd;
        }
        if (rm > half) {
            const cd = { kind: 'count-overflow', orientation: 'row', line: r, value: MOON, count: rm, cells: rmCells };
            if (accept(cd)) return cd;
        }
        let cs = 0, cm = 0;
        const csCells = [], cmCells = [];
        for (let i = 0; i < N; i++) {
            if (filled[i][c] === SUN) { cs++; csCells.push([i, c]); }
            else if (filled[i][c] === MOON) { cm++; cmCells.push([i, c]); }
        }
        if (cs > half) {
            const cd = { kind: 'count-overflow', orientation: 'col', line: c, value: SUN, count: cs, cells: csCells };
            if (accept(cd)) return cd;
        }
        if (cm > half) {
            const cd = { kind: 'count-overflow', orientation: 'col', line: c, value: MOON, count: cm, cells: cmCells };
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
    // L2 / L3 / L4 deductions — hypothesize + L1 fixpoint, scored by
    // *minimum* chain length via backward closure.
    //
    // Pipeline for every cell (r, c):
    //   1. Hypothesise X = v at (r, c). (If L1 already refutes v at
    //      (r, c), that's an L1 cell — skip.)
    //   2. Propagate L1 to fixpoint within the tier's scope.
    //      - L2 / L3 : single line (row r OR col c, picked separately
    //                  per attempt).
    //      - L4      : anywhere on the board.
    //   3. Enumerate ALL in-scope contradictions in the post-fixpoint
    //      board.
    //   4. For each contradiction, walk backward through every placed
    //      cell's `reason.sources` to compute the MINIMUM set of L1
    //      placements actually required to derive that contradiction.
    //      The chain length is that minimum, not the trace length.
    //   5. Across all contradictions found, take the contradiction
    //      with the smallest chain length.
    //
    // Tier classification by minimum chain length:
    //   L2 = single-line, min chain == 1
    //   L3 = single-line, min chain >= 2
    //   L4 = anywhere,   1 <= min chain <= L4_BUDGET
    //
    // L4 is a superset of L2/L3 in raw coverage, so the disjoint-set
    // wrappers (findL{K}ErasableCells / nextDeduction) classify each
    // cell at the LOWEST applicable tier.
    //
    // Reason shape (every L>=2 reason):
    //   { kind: 'L2'|'L3'|'L4',
    //     hypothesis: { cell: [r, c], value: triedValue },
    //     propagation: [{ cell, value, reason: <L1 reason> }, ...],
    //         // ^ the minimal chain, in original propagation order
    //     contradiction: <see findContradictionAt>,
    //     chainLength: int,            // == propagation.length
    //     orientation: 'row'|'col',    // L2/L3 only — which line carried the chain
    //     budget: int,                 // L4 only — the K cap
    //     value }
    // -----------------------------------------------------------------

    const L4_BUDGET = 5;

    /**
     * Enumerate every contradiction visible in the current filled state.
     * Used after running L1 to fixpoint inside a hypothesis attempt.
     *
     * The optional `predicate` filters contradictions before they're
     * returned (e.g. L2/L3 keep only those in their single line).
     */
    function findAllContradictions(filled, wallIndex, N, predicate) {
        const accept = predicate || (() => true);
        const half = N / 2;
        const out = [];

        // Count overflow per row.
        for (let r = 0; r < N; r++) {
            let rs = 0, rm = 0;
            const rsCells = [], rmCells = [];
            for (let j = 0; j < N; j++) {
                if (filled[r][j] === SUN) { rs++; rsCells.push([r, j]); }
                else if (filled[r][j] === MOON) { rm++; rmCells.push([r, j]); }
            }
            if (rs > half) {
                const cd = { kind: 'count-overflow', orientation: 'row',
                    line: r, value: SUN, count: rs, cells: rsCells };
                if (accept(cd)) out.push(cd);
            }
            if (rm > half) {
                const cd = { kind: 'count-overflow', orientation: 'row',
                    line: r, value: MOON, count: rm, cells: rmCells };
                if (accept(cd)) out.push(cd);
            }
        }
        // Count overflow per column.
        for (let c = 0; c < N; c++) {
            let cs = 0, cm = 0;
            const csCells = [], cmCells = [];
            for (let i = 0; i < N; i++) {
                if (filled[i][c] === SUN) { cs++; csCells.push([i, c]); }
                else if (filled[i][c] === MOON) { cm++; cmCells.push([i, c]); }
            }
            if (cs > half) {
                const cd = { kind: 'count-overflow', orientation: 'col',
                    line: c, value: SUN, count: cs, cells: csCells };
                if (accept(cd)) out.push(cd);
            }
            if (cm > half) {
                const cd = { kind: 'count-overflow', orientation: 'col',
                    line: c, value: MOON, count: cm, cells: cmCells };
                if (accept(cd)) out.push(cd);
            }
        }

        // Three-in-row, every horizontal window.
        for (let r = 0; r < N; r++) {
            for (let c = 0; c + 2 < N; c++) {
                const v = filled[r][c];
                if (v !== 0 && filled[r][c + 1] === v && filled[r][c + 2] === v) {
                    const cd = { kind: 'three-in-row', orientation: 'row',
                        cells: [[r, c], [r, c + 1], [r, c + 2]], value: v };
                    if (accept(cd)) out.push(cd);
                }
            }
        }
        // Three-in-row, every vertical window.
        for (let c = 0; c < N; c++) {
            for (let r = 0; r + 2 < N; r++) {
                const v = filled[r][c];
                if (v !== 0 && filled[r + 1][c] === v && filled[r + 2][c] === v) {
                    const cd = { kind: 'three-in-row', orientation: 'col',
                        cells: [[r, c], [r + 1, c], [r + 2, c]], value: v };
                    if (accept(cd)) out.push(cd);
                }
            }
        }

        // Walls — iterate byCell and dedupe pairs.
        const seenPair = new Set();
        for (const [k1, neighbors] of wallIndex.byCell) {
            const r1 = Math.floor(k1 / 100), c1 = k1 % 100;
            for (const { kind, otherR: r2, otherC: c2 } of neighbors) {
                const k2 = cellKey(r2, c2);
                const pairKey = k1 < k2 ? `${k1}|${k2}` : `${k2}|${k1}`;
                if (seenPair.has(pairKey)) continue;
                seenPair.add(pairKey);
                const v1 = filled[r1][c1], v2 = filled[r2][c2];
                if (v1 === 0 || v2 === 0) continue;
                if (kind === 'same' && v1 !== v2) {
                    const cd = { kind: 'wall', wallKind: 'same',
                        cells: [[r1, c1], [r2, c2]], values: [v1, v2] };
                    if (accept(cd)) out.push(cd);
                }
                if (kind === 'diff' && v1 === v2) {
                    const cd = { kind: 'wall', wallKind: 'diff',
                        cells: [[r1, c1], [r2, c2]], values: [v1, v2] };
                    if (accept(cd)) out.push(cd);
                }
            }
        }
        return out;
    }

    /**
     * Backward dependency closure.
     *
     * Given the propagation trace of a successful refutation and ONE
     * contradiction it produced, walk backward from the contradiction's
     * cells: for every cell we've added to `needed`, also add any of
     * its L1 rule's `sources` that themselves came from the trace
     * (prefill cells and the hypothesis cell are excluded — they're
     * "given", not chain steps).
     *
     * Returns:
     *   { chainSteps: [{cell, value, reason}, ...],  // in propagation order
     *     chainLength: int }                         // == chainSteps.length
     *
     * The returned chain is the smallest subset of the trace whose
     * placements jointly justify the contradiction.
     */
    function backwardClose(trace, contradiction, hypothesisCell) {
        const stepByKey = new Map();
        for (const step of trace) {
            stepByKey.set(cellKey(step.cell[0], step.cell[1]), step);
        }
        const hypKey = cellKey(hypothesisCell[0], hypothesisCell[1]);
        const needed = new Set();
        const queue = [];
        const add = (rr, cc) => {
            const key = cellKey(rr, cc);
            if (key === hypKey) return;
            if (!stepByKey.has(key)) return;     // prefill — given
            if (needed.has(key)) return;
            needed.add(key);
            queue.push(key);
        };
        for (const [rr, cc] of (contradiction.cells || [])) add(rr, cc);
        while (queue.length) {
            const key = queue.shift();
            const step = stepByKey.get(key);
            for (const [sr, sc] of (step.reason.sources || [])) add(sr, sc);
        }
        // Preserve original propagation order.
        const chainSteps = trace.filter(
            (s) => needed.has(cellKey(s.cell[0], s.cell[1])));
        return { chainSteps, chainLength: chainSteps.length };
    }

    /**
     * Across every contradiction in `contradictions`, return the
     * (contradiction, chainSteps, chainLength) whose chain cost is
     * the SHORTEST. `costFn(chainSteps)` defaults to `chainSteps.length`
     * — pass a different function (e.g. L4's wall-chain discount) to
     * change how chain length is scored.
     *
     * Returns null if `contradictions` is empty.
     */
    function pickShortestChain(trace, contradictions, hypothesisCell, costFn) {
        const cost = costFn || ((steps) => steps.length);
        let best = null;
        for (const cd of contradictions) {
            const closed = backwardClose(trace, cd, hypothesisCell);
            const chainLength = cost(closed.chainSteps);
            if (!best || chainLength < best.chainLength) {
                best = { contradiction: cd, chainSteps: closed.chainSteps, chainLength };
            }
        }
        return best;
    }

    /**
     * L4-specific chain cost: T-wall placements that sit in the same
     * connected component of the puzzle's wall graph are grouped
     * together, and a group of K placements costs `ceil(K/3)` instead
     * of K. Non-T-wall placements (T-count, T-three) each cost 1.
     *
     * Grouping by the puzzle's wall graph (instead of by propagation
     * source links) is monotonic: adding cells to the base state can
     * only shrink the set of T-wall placements in each component, never
     * split a component into two. That avoids the case where a wall
     * chain Y1–Y2–Y3 was scored as cost 1 in a richer state but jumped
     * to cost 2 in a poorer state because the middle cell happened to
     * be filled there.
     *
     * Rationale: a chain of walls is visually mechanical — the player
     * follows the walls hand-over-hand, and a pre-filled cell in the
     * middle of the chain is exactly the kind of "free stepping stone"
     * a player would happily skip over. We treat every 3 wall hops as
     * one cognitive step inside L4's budget regardless of whether the
     * in-between cells came from this propagation or from the base.
     */
    function chainCostWithWallDiscount(chainSteps, wallComponentOf) {
        if (chainSteps.length === 0) return 0;
        const wallSizes = new Map();
        let nonWallCount = 0;
        for (const s of chainSteps) {
            if (s.reason.kind === 'T-wall' && wallComponentOf) {
                const cid = wallComponentOf(s.cell[0], s.cell[1]);
                wallSizes.set(cid, (wallSizes.get(cid) || 0) + 1);
            } else {
                nonWallCount += 1;
            }
        }
        let cost = nonWallCount;
        for (const size of wallSizes.values()) {
            cost += Math.ceil(size / 3);
        }
        return cost;
    }

    /**
     * Single-line hypothesis: hypothesise (r, c) along `orientation`,
     * propagate L1 to fixpoint restricted to that line, scan in-line
     * contradictions, return the shortest backward-closed chain (or
     * null if neither value of (r, c) refutes itself in-line).
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
                if (cd.orientation === 'row') return isRow && cd.cells[0][0] === r;
                return !isRow && cd.cells[0][1] === c;
            }
            return cd.cells.every(([rr, cc]) => inScope(rr, cc));
        };

        for (const tryV of [SUN, MOON]) {
            const f = filled.map((row) => row.slice());
            f[r][c] = tryV;
            if (findContradictionAt(r, c, f, wallIndex, N)) continue;  // L1

            const trace = [];
            let progressed = true;
            while (progressed) {
                progressed = false;
                if (isRow) {
                    for (let cc = 0; cc < N; cc++) {
                        if (f[r][cc] !== 0) continue;
                        const e = l1Explain(r, cc, f, wallIndex, N);
                        if (!e) continue;
                        f[r][cc] = e.value;
                        trace.push({ cell: [r, cc], value: e.value, reason: e.reason });
                        progressed = true;
                    }
                } else {
                    for (let rr = 0; rr < N; rr++) {
                        if (f[rr][c] !== 0) continue;
                        const e = l1Explain(rr, c, f, wallIndex, N);
                        if (!e) continue;
                        f[rr][c] = e.value;
                        trace.push({ cell: [rr, c], value: e.value, reason: e.reason });
                        progressed = true;
                    }
                }
            }

            const allCd = findAllContradictions(f, wallIndex, N, contradictionInScope);
            if (allCd.length === 0) continue;
            const shortest = pickShortestChain(trace, allCd, [r, c]);
            if (!shortest) continue;

            const value = tryV === SUN ? MOON : SUN;
            return {
                value,
                triedValue: tryV,
                chainLength: shortest.chainLength,
                propagation: shortest.chainSteps,
                contradiction: shortest.contradiction,
                orientation,
            };
        }
        return null;
    }

    /**
     * Run single-line propagation in BOTH orientations (row r and
     * col c) and return whichever yields the shorter backward-closed
     * chain. Returns null if neither orientation refutes.
     */
    function bestSingleLineHypothesis(r, c, filled, wallIndex, N) {
        let best = null;
        for (const orient of ['row', 'col']) {
            const e = singleLineHypothesisExplain(r, c, filled, wallIndex, N, orient);
            if (!e) continue;
            if (!best || e.chainLength < best.chainLength) best = e;
        }
        return best;
    }

    function l2Explain(r, c, filled, wallIndex, N) {
        const e = bestSingleLineHypothesis(r, c, filled, wallIndex, N);
        if (!e || e.chainLength !== 1) return null;
        return {
            value: e.value,
            reason: {
                kind: 'L2',
                hypothesis: { cell: [r, c], value: e.triedValue },
                propagation: e.propagation,
                contradiction: e.contradiction,
                chainLength: e.chainLength,
                orientation: e.orientation,
                value: e.value,
            },
        };
    }

    function l3Explain(r, c, filled, wallIndex, N) {
        const e = bestSingleLineHypothesis(r, c, filled, wallIndex, N);
        if (!e || e.chainLength < 2) return null;
        return {
            value: e.value,
            reason: {
                kind: 'L3',
                hypothesis: { cell: [r, c], value: e.triedValue },
                propagation: e.propagation,
                contradiction: e.contradiction,
                chainLength: e.chainLength,
                orientation: e.orientation,
                value: e.value,
            },
        };
    }

    /**
     * L4 = anywhere-on-board L1 propagation, capped at `L4_BUDGET`
     * essential placements (i.e. backward-closed chain length, scored
     * with the wall-chain discount).
     *
     * Hypothesise (r, c) = v, propagate L1 anywhere to fixpoint, scan
     * all contradictions, take the chain whose `chainCostWithWallDiscount`
     * is shortest. If that cost fits the budget, the cell is L4.
     *
     * `chainLength` in the returned reason is the discounted cost;
     * `rawChainLength` is the literal placement count (useful for
     * display and debug).
     */
    function l4Explain(r, c, filled, wallIndex, N) {
        for (const tryV of [SUN, MOON]) {
            const f = filled.map((row) => row.slice());
            f[r][c] = tryV;
            if (findContradictionAt(r, c, f, wallIndex, N)) continue;  // L1

            const trace = [];
            let progressed = true;
            while (progressed) {
                progressed = false;
                for (let rr = 0; rr < N; rr++) {
                    for (let cc = 0; cc < N; cc++) {
                        if (f[rr][cc] !== 0) continue;
                        const e = l1Explain(rr, cc, f, wallIndex, N);
                        if (!e) continue;
                        f[rr][cc] = e.value;
                        trace.push({ cell: [rr, cc], value: e.value, reason: e.reason });
                        progressed = true;
                    }
                }
            }

            const allCd = findAllContradictions(f, wallIndex, N);
            if (allCd.length === 0) continue;
            const shortest = pickShortestChain(trace, allCd, [r, c],
                (steps) => chainCostWithWallDiscount(steps, wallIndex.wallComponentOf));
            if (!shortest) continue;
            if (shortest.chainLength > L4_BUDGET) continue;

            const value = tryV === SUN ? MOON : SUN;
            return {
                value,
                reason: {
                    kind: 'L4',
                    hypothesis: { cell: [r, c], value: tryV },
                    propagation: shortest.chainSteps,
                    contradiction: shortest.contradiction,
                    chainLength: shortest.chainLength,
                    rawChainLength: shortest.chainSteps.length,
                    budget: L4_BUDGET,
                    value,
                },
            };
        }
        return null;
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
        // Hard candidates fail verifySolvable occasionally because the
        // erase-time L_K checks are local — a cell that's L4-solvable
        // mid-erasure may not be once *every* other erasable cell is
        // gone. We treat those as throwaways and keep sampling; if we
        // run out, we fall back to the best unverified candidate so
        // the UI always gets something to show.
        const maxAttempts = wantsRetry ? 30 : 1;

        let best = null;            // best verified
        let bestUnverified = null;  // fallback if no verified found
        let attemptsUsed = 0;
        for (let a = 0; a < maxAttempts; a++) {
            attemptsUsed = a + 1;
            const attemptSeed = (seed + a * 0x9e3779b9) >>> 0;
            const cand = generateOnce(size, difficulty, attemptSeed);
            if (cand.stats.verified) {
                if (!best || scoreOf(cand) > scoreOf(best)) best = cand;
            } else if (!bestUnverified
                || scoreOf(cand) > scoreOf(bestUnverified)) {
                bestUnverified = cand;
            }
            if (best && scoreOf(best) >= target) break;
        }
        const result = best || bestUnverified;
        result.stats.attemptsUsed = attemptsUsed;
        if (!best) {
            console.warn('[tango-gen] no verified candidate after',
                attemptsUsed, 'attempts; returning unverified',
                result.id);
        }
        return result;
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
        const verified = verifySolvable(filled, walls, solution, N, params.tactics);
        puzzle.stats.verified = verified;
        if (!verified) {
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
