/**
 * Tango puzzle generator — constructive, logic-solvable.
 *
 * Strategy (all three difficulties)
 * ---------------------------------
 * 1. Sample a uniform random complete legal solution (see the
 *    `randomSolution` block for the two-mode sampler).
 * 2. Build a max-constraint puzzle from that solution: every cell
 *    pre-filled, every adjacent boundary carrying its compatible
 *    `=` / `×` wall.
 * 3. Iteratively remove constraints (one cell value or one wall at
 *    a time) using a weighted-randomised "longest-survivor" score
 *    `(h + 1) · kindWeight · noise`, where `h` counts how many
 *    times the constraint has previously survived a removal attempt.
 *    After each tentative removal we re-run `verifySolvable` and
 *    only commit the removal if the puzzle is still solvable using
 *    the difficulty's allowed tactic tiers.
 * 4. Score the resulting puzzle by `tierScore`: a weighted sum over
 *    how many cells the solver had to derive at each tier, with
 *    L4 weighted dynamically by `log10(E) · N` per step.
 *
 * Difficulty wiring
 * -----------------
 *   Easy   – single carve, then back-fill the last few removals so
 *            the player gets back a chunk of "hardest" constraints
 *            (controlled by `easyBackfillCount`).
 *   Medium – best of K carves (K_max = hard/2), bias-driven schedule.
 *   Hard   – best of K carves (K_max = 30 / 10 / 5 for 6 / 8 / 10).
 *
 * For Medium / Hard each generation samples one `batchBias ∈ U(0, 1)`
 * which drives both the per-batch (wCell, wWall) weights and the
 * actual K. See `generateFromMaxOnSolution` for the formulas.
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
 *   L2   single-line hypothesis, minimum-chain = 1 (one L1 step away
 *        from contradiction).
 *   L3   single-line hypothesis, minimum-chain ≥ 2.
 *   L4   anywhere-on-board hypothesis, minimum-chain ≤ L4_BUDGET, with
 *        a wall-chain discount (consecutive T-wall placements in the
 *        chain count as ceil(K/3) since they're visually mechanical).
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;
    const SUN = 1;
    const MOON = 2;

    // -----------------------------------------------------------------
    // Random complete solution.
    //
    // We've verified empirically (see git history for the analysis
    // tool that lived under tools/) that naive cell-by-cell first-
    // success backtracking is *badly* biased — on 6×6 the worst
    // board appears ~10000× more often than the rarest. Two effects
    // combine to produce this: the row-major scan order, and the
    // "if it can complete, take it" choice rule that favours the
    // larger subtree at every branch point.
    //
    // What we ship instead:
    //
    //   • For N ≤ 8: row-pattern rejection sampling. There are
    //     only 14 valid row patterns at N=6 and ~36 at N=8, so we
    //     enumerate them once, draw N independent row patterns,
    //     and check column constraints. Each accept gives a sample
    //     drawn exactly uniformly from the set of valid Tango
    //     solutions. Accept rate is ~0.15% at N=6 and ~10^-6 at
    //     N=8; per sample we expect ~700 trials at N=6 and ~10^6
    //     at N=8, both well under a millisecond per sample.
    //
    //   • For N = 10: rejection is infeasible (accept rate ≈ 10^-10
    //     → hours per sample). We use row-pattern *backtracking*
    //     to seed a valid board cheaply, then run a Markov chain
    //     over valid boards using three move types: 2×2 anti-
    //     diagonal flip, whole-row swap, and whole-column swap.
    //     All three preserve row/column counts; the chain rejects
    //     a move only when no-three would break. 500K mixing steps
    //     pulls the distribution comfortably into "indistinguishable
    //     from uniform" territory under our analysis tool's chi²
    //     test (verified at N=6, where we have ground truth).
    // -----------------------------------------------------------------

    const validRowPatternsCache = new Map();
    function getValidRowPatterns(N) {
        if (validRowPatternsCache.has(N)) return validRowPatternsCache.get(N);
        const half = N / 2;
        const out = [];
        // Enumerate all length-N binary strings with exactly `half`
        // suns, then keep only those with no run of three.
        const idx = new Array(half);
        for (let i = 0; i < half; i++) idx[i] = i;
        while (true) {
            const pat = new Array(N).fill(MOON);
            for (let i = 0; i < half; i++) pat[idx[i]] = SUN;
            let bad = false;
            for (let i = 0; i + 2 < N; i++) {
                if (pat[i] === pat[i+1] && pat[i+1] === pat[i+2]) { bad = true; break; }
            }
            if (!bad) out.push(pat);
            let i = half - 1;
            while (i >= 0 && idx[i] === N - half + i) i--;
            if (i < 0) break;
            idx[i]++;
            for (let j = i + 1; j < half; j++) idx[j] = idx[j-1] + 1;
        }
        validRowPatternsCache.set(N, out);
        return out;
    }

    // L — exact-uniform sampler via row-pattern rejection.
    // Returns null if the rare-but-bounded retry budget is exhausted.
    function sampleByRowRejection(N, rng) {
        const half = N / 2;
        const patterns = getValidRowPatterns(N);
        const M = patterns.length;
        // 25M attempts ≈ 5 s wall clock at ~200 ns / attempt.
        // For 6×6 the fail probability is e^(-25M * 0.0015) ≈ 10^-130;
        // for 8×8 it's e^(-25M * 10^-6) ≈ 10^-11. Both are negligible
        // in practice — the bound exists so a pathological seed can't
        // wedge the UI thread, not because we expect it to trigger.
        const MAX_ATTEMPTS = 25_000_000;
        const g = new Array(N);
        for (let attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
            for (let r = 0; r < N; r++) {
                g[r] = patterns[(rng() * M) | 0];
            }
            let ok = true;
            for (let c = 0; c < N && ok; c++) {
                let sunCount = 0;
                for (let r = 0; r < N; r++) {
                    if (g[r][c] === SUN) sunCount += 1;
                }
                if (sunCount !== half) { ok = false; break; }
                for (let r = 0; r + 2 < N && ok; r++) {
                    if (g[r][c] === g[r+1][c] && g[r+1][c] === g[r+2][c]) {
                        ok = false;
                    }
                }
            }
            if (ok) {
                return g.map((row) => row.slice());
            }
        }
        return null;
    }

    // M — row-pattern backtracking. Used as the MCMC seed for N=10.
    // Still biased (first-success at row granularity) but very fast.
    function sampleByRowBacktrack(N, rng) {
        const half = N / 2;
        const patterns = getValidRowPatterns(N);
        const M = patterns.length;
        const grid = new Array(N);
        const colSun = new Array(N).fill(0);
        const colMoon = new Array(N).fill(0);
        const colLast = new Array(N).fill(0);
        const colRun = new Array(N).fill(0);
        const patOrder = new Array(M);
        for (let i = 0; i < M; i++) patOrder[i] = i;
        function fitsRow(pat) {
            for (let c = 0; c < N; c++) {
                const v = pat[c];
                if (v === SUN && colSun[c] >= half) return false;
                if (v === MOON && colMoon[c] >= half) return false;
                if (colLast[c] === v && colRun[c] >= 2) return false;
            }
            return true;
        }
        function applyRow(pat) {
            const prevLast = colLast.slice();
            const prevRun = colRun.slice();
            for (let c = 0; c < N; c++) {
                const v = pat[c];
                if (v === SUN) colSun[c]++; else colMoon[c]++;
                if (colLast[c] === v) colRun[c]++;
                else { colLast[c] = v; colRun[c] = 1; }
            }
            return { prevLast, prevRun };
        }
        function undoRow(pat, snap) {
            for (let c = 0; c < N; c++) {
                if (pat[c] === SUN) colSun[c]--; else colMoon[c]--;
                colLast[c] = snap.prevLast[c];
                colRun[c] = snap.prevRun[c];
            }
        }
        function solve(r) {
            if (r === N) return true;
            PC.rng.shuffle(patOrder, rng);
            for (let i = 0; i < M; i++) {
                const pat = patterns[patOrder[i]];
                if (!fitsRow(pat)) continue;
                const snap = applyRow(pat);
                grid[r] = pat;
                if (solve(r + 1)) return true;
                grid[r] = undefined;
                undoRow(pat, snap);
            }
            return false;
        }
        return solve(0) ? grid.map((row) => row.slice()) : null;
    }

    // -----------------------------------------------------------------
    // MCMC mixing — three move types, all preserve row & col counts.
    //   2×2 flip   : A B / B A  →  B A / A B
    //   row swap   : swap two whole rows
    //   col swap   : swap two whole columns
    // After any move, check the relevant no-three constraint; revert
    // on violation. Detailed balance holds because each move is its
    // own inverse and selection is uniform.
    // -----------------------------------------------------------------
    function colNoThreeAt(g, c, N) {
        for (let r = 0; r + 2 < N; r++) {
            if (g[r][c] === g[r+1][c] && g[r+1][c] === g[r+2][c]) return false;
        }
        return true;
    }
    function rowNoThreeAt(g, r, N) {
        for (let c = 0; c + 2 < N; c++) {
            if (g[r][c] === g[r][c+1] && g[r][c+1] === g[r][c+2]) return false;
        }
        return true;
    }
    function mcmcMix(g, rng, steps) {
        const N = g.length;
        for (let step = 0; step < steps; step++) {
            const which = rng();
            if (which < 0.5) {
                const r1 = (rng() * N) | 0;
                const r2 = (rng() * N) | 0;
                if (r1 === r2) continue;
                const c1 = (rng() * N) | 0;
                const c2 = (rng() * N) | 0;
                if (c1 === c2) continue;
                const a = g[r1][c1], b = g[r1][c2];
                if (a === b) continue;
                if (g[r2][c1] !== b || g[r2][c2] !== a) continue;
                g[r1][c1] = b; g[r1][c2] = a;
                g[r2][c1] = a; g[r2][c2] = b;
                if (!(colNoThreeAt(g, c1, N) && colNoThreeAt(g, c2, N)
                    && rowNoThreeAt(g, r1, N) && rowNoThreeAt(g, r2, N))) {
                    g[r1][c1] = a; g[r1][c2] = b;
                    g[r2][c1] = b; g[r2][c2] = a;
                }
            } else if (which < 0.75) {
                const r1 = (rng() * N) | 0;
                const r2 = (rng() * N) | 0;
                if (r1 === r2) continue;
                const tmp = g[r1]; g[r1] = g[r2]; g[r2] = tmp;
                // Row swap only re-orders rows; the columns are the
                // only place no-three can break.
                let ok = true;
                for (let c = 0; c < N && ok; c++) {
                    if (!colNoThreeAt(g, c, N)) ok = false;
                }
                if (!ok) {
                    const t = g[r1]; g[r1] = g[r2]; g[r2] = t;
                }
            } else {
                const c1 = (rng() * N) | 0;
                const c2 = (rng() * N) | 0;
                if (c1 === c2) continue;
                for (let r = 0; r < N; r++) {
                    const t = g[r][c1]; g[r][c1] = g[r][c2]; g[r][c2] = t;
                }
                let ok = true;
                for (let r = 0; r < N && ok; r++) {
                    if (!rowNoThreeAt(g, r, N)) ok = false;
                }
                if (!ok) {
                    for (let r = 0; r < N; r++) {
                        const t = g[r][c1]; g[r][c1] = g[r][c2]; g[r][c2] = t;
                    }
                }
            }
        }
        return g;
    }

    // Per-size MCMC step budget. The 6/8 numbers only matter if
    // `sampleByRowRejection` ever falls back (it basically never
    // does); 10's value is the one that actually runs in production.
    function mcmcStepsFor(N) {
        if (N <= 6) return 20_000;
        if (N <= 8) return 100_000;
        return 500_000;
    }

    function randomSolution(N, rng) {
        if (N <= 8) {
            const g = sampleByRowRejection(N, rng);
            if (g) return g;
            console.warn('[tango-gen] row-rejection budget exhausted at N=' + N
                + '; falling back to MCMC sampler');
        }
        const seed = sampleByRowBacktrack(N, rng);
        if (!seed) return null;
        return mcmcMix(seed, rng, mcmcStepsFor(N));
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
    //   tactics : which tactic tiers the puzzle is allowed to need.
    //             Easy   = L1 + L2 — direct rules, plus one-step
    //                      line-bounded hypotheses (still feels L1-y).
    //             Medium = + L3   — multi-step line hypotheses.
    //             Hard   = + L4   — cross-board hypotheses.
    //
    // The carve loop reads only `tactics` (everything else — K, the
    // batch bias, scoring — is driven by `startFromMaxBudget` and
    // `generateFromMaxOnSolution`).
    // -----------------------------------------------------------------

    function difficultyParams(N, difficulty) {
        if (difficulty === 'easy')   return { tactics: ['L1', 'L2'] };
        if (difficulty === 'hard')   return { tactics: ['L1', 'L2', 'L3', 'L4'] };
        return { tactics: ['L1', 'L2', 'L3'] };
    }

    // -----------------------------------------------------------------
    // Main entry point.
    //
    // All three difficulties share the same generator: sample a
    // uniform random solution, then run K start-from-max carves
    // against it (each carve tactic-bounded by the difficulty's
    // allowed tiers) and return the puzzle whose final state has the
    // highest weighted tier-breakdown score. K is bounded per
    // (N, difficulty) — see `startFromMaxBudget` — so the caller can
    // drive a determinate progress bar.
    //
    // `onProgress` is optional. When supplied it's awaited as
    //     await onProgress(fraction /* 0..1 */)
    // after each completed carve, giving the UI a chance to repaint.
    // -----------------------------------------------------------------

    async function generate(size, difficulty, seed, onProgress) {
        const result = await generateOnce(size, difficulty, seed, onProgress);
        if (!result.stats.verified) {
            console.warn('[tango-gen] returning unverified', result.id);
        }
        return result;
    }

    // Per-(N, difficulty) maximum K for the inner start-from-max
    // loop. Easy is single-shot — see generateFromMaxOnSolution's
    // easy branch, which back-fills the last few removals instead
    // of K-selecting. Medium gets half of hard's budget.
    function startFromMaxBudget(N, difficulty) {
        if (difficulty === 'easy') return 1;
        const hard = N <= 6 ? 30 : N <= 8 ? 10 : 5;
        if (difficulty === 'medium') return Math.max(1, Math.round(hard / 2));
        return hard;
    }

    // Static per-cell weights for L1 / L2 / L3 — see tierScore. L4
    // is dynamic and weighted per inference step (see
    // buildTierBreakdown's l4Score accumulator), so it doesn't
    // appear here.
    function tierWeights(N) {
        return {
            L1: 1,
            L2: 1.5,
            L3: N / 2,
        };
    }

    // Returns a function that, given (filled, walls), walks the
    // actual solver step-by-step (lowest allowed tier first, same
    // policy as verifySolvable) and reports how each cell got
    // derived:
    //   l1Count, l2Count, l3Count : # cells filled at that tier
    //   l4Count                    : # cells filled at L4
    //   l4Score                    : Σ log10(E) * N, where E is the
    //                                empty-cell count at the moment
    //                                that L4 step fires (including
    //                                the L4 target itself).
    //   unreachable               : cells the allowed tactics can't
    //                                reach (always 0 for verified
    //                                puzzles).
    // L4 weight scales as `log10(E) * N` so it typically sits in
    // the 2× – 4× L3 range — bigger boards / sparser puzzles weight
    // L4 more, but the log keeps it from exploding.
    function buildTierBreakdown(N, tactics) {
        const has = { L1: true, L2: false, L3: false, L4: false };
        for (const t of tactics) has[t] = true;
        const tierFn = {
            L1: l1ForcedAt,
            L2: l2ForcedAt,
            L3: l3ForcedAt,
            L4: l4ForcedAt,
        };
        const tierOrder = ['L1', 'L2', 'L3', 'L4'].filter((t) => has[t]);

        return (filled, walls) => {
            const f = filled.map((row) => row.slice());
            const idx = buildWallIndex(walls);
            let emptyCount = 0;
            for (const row of f) for (const v of row) if (v === 0) emptyCount++;

            let l1Count = 0, l2Count = 0, l3Count = 0, l4Count = 0;
            let l4Score = 0;

            let progressed = true;
            while (progressed) {
                progressed = false;
                for (const tier of tierOrder) {
                    const fn = tierFn[tier];
                    for (let r = 0; r < N; r++) {
                        for (let c = 0; c < N; c++) {
                            if (f[r][c] !== 0) continue;
                            const v = fn(r, c, f, idx, N);
                            if (v === 0) continue;
                            if (tier === 'L1') l1Count++;
                            else if (tier === 'L2') l2Count++;
                            else if (tier === 'L3') l3Count++;
                            else {
                                l4Count++;
                                // emptyCount currently includes the
                                // cell we're about to fill (the L4
                                // target itself), per the user spec.
                                l4Score += Math.log10(Math.max(2, emptyCount)) * N;
                            }
                            f[r][c] = v;
                            emptyCount--;
                            progressed = true;
                        }
                    }
                    if (progressed) break;
                }
            }
            return {
                l1Count, l2Count, l3Count, l4Count,
                l4Score,
                unreachable: emptyCount,
            };
        };
    }

    function tierScore(breakdown, weights) {
        return breakdown.l1Count * weights.L1
             + breakdown.l2Count * weights.L2
             + breakdown.l3Count * weights.L3
             + breakdown.l4Score;
    }

    // Run a single start-from-max carve against `solution`. Builds the
    // maximum constraint set (every cell prefilled, every adjacent pair
    // walled to match the solution), then in each pass scores every
    // remaining constraint by `(score + 1) * kindWeight * noise`,
    // sorts descending, and walks the list committing removals that
    // survive `verifySolvable`. Loops until a pass removes nothing.
    //
    // `wCell` / `wWall` are passed in by the caller — the batch
    // policy (see generateFromMaxOnSolution) decides the cell/wall
    // preference once and reuses it for every K-run. The returned
    // `removalLog` is the ordered list of successful removals so
    // the caller can back-fill (used by easy to roll back the
    // hardest few decisions).
    function carveFromMaxOnce(N, params, solution, rng, wCell, wWall) {
        const filled = solution.map((row) => row.slice());
        const pairs = adjacentPairs(N);
        const walls = pairs.map(([r1, c1, r2, c2]) => ({
            r1, c1, r2, c2,
            kind: solution[r1][c1] === solution[r2][c2] ? 'same' : 'diff',
        }));

        const weights = tierWeights(N);
        const breakdown = buildTierBreakdown(N, params.tactics);
        const scoreNow = () => tierScore(breakdown(filled, walls), weights);

        const stats = {
            passes: 0, attempts: 0,
            cellsRemoved: 0, wallsRemoved: 0,
            weightCell: +wCell.toFixed(3),
            weightWall: +wWall.toFixed(3),
        };
        const removalLog = [];

        while (true) {
            stats.passes++;
            const cands = [];
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (filled[r][c] !== 0) cands.push({ kind: 'cell', r, c });
                }
            }
            for (const w of walls) cands.push({ kind: 'wall', wall: w });

            // Score every candidate: tentative-remove → hardness →
            // restore. Solvability isn't gated here — even an
            // unsolvable removal has a hardness number; the real gate
            // is verifySolvable in the try-pass below.
            for (const cand of cands) {
                let restore;
                if (cand.kind === 'cell') {
                    const v = filled[cand.r][cand.c];
                    filled[cand.r][cand.c] = 0;
                    restore = () => { filled[cand.r][cand.c] = v; };
                } else {
                    const idx = walls.indexOf(cand.wall);
                    walls.splice(idx, 1);
                    restore = () => { walls.splice(idx, 0, cand.wall); };
                }
                const h = scoreNow();
                restore();
                const w = cand.kind === 'cell' ? wCell : wWall;
                const noise = 0.5 + rng() * 1.5;
                cand.score = (h + 1) * w * noise;
            }
            cands.sort((a, b) => b.score - a.score);

            let removed = 0;
            for (const cand of cands) {
                stats.attempts++;
                let restore;
                if (cand.kind === 'cell') {
                    const v = filled[cand.r][cand.c];
                    if (v === 0) continue;
                    filled[cand.r][cand.c] = 0;
                    restore = () => { filled[cand.r][cand.c] = v; };
                } else {
                    const idx = walls.indexOf(cand.wall);
                    if (idx < 0) continue;
                    walls.splice(idx, 1);
                    restore = () => { walls.splice(idx, 0, cand.wall); };
                }
                if (verifySolvable(filled, walls, solution, N, params.tactics)) {
                    removed++;
                    if (cand.kind === 'cell') {
                        stats.cellsRemoved++;
                        removalLog.push({ kind: 'cell', r: cand.r, c: cand.c });
                    } else {
                        stats.wallsRemoved++;
                        removalLog.push({ kind: 'wall', wall: cand.wall });
                    }
                } else {
                    restore();
                }
            }
            if (removed === 0) break;
        }

        return { filled, walls, stats, removalLog };
    }

    // Build the final puzzle envelope around a finished carve.
    // Factored out so easy (single carve + back-fill) and the
    // medium/hard K-loop don't need to duplicate the stats block.
    function buildPuzzleFromCarve(N, difficulty, seed, solution, params,
            carve, metrics, plannedK, actualK, batchBias) {
        const { filled, walls, stats: carveStats } = carve;
        const prefillCount = filled.flat().filter((v) => v !== 0).length;
        const puzzle = {
            id: `tango-${N}x${N}-${difficulty}-${seed.toString(36)}`,
            game: 'tango',
            size: N,
            difficulty,
            prefilled: filled,
            walls,
            solution,
            stats: {
                prefillCount,
                wallCount: walls.length,
                // Per-tier "exactly first-classified at this tier"
                // counts from the solver walk.
                l1OnlyCells: metrics.l1Count,
                l2OnlyCells: metrics.l2Count,
                l3OnlyCells: metrics.l3Count,
                l4OnlyCells: metrics.l4Count,
                l4Score: +metrics.l4Score.toFixed(3),
                // Aggregate "≥ tier required" counters retained for
                // back-compat with the stats / debug tooling.
                l2OrAboveRequiredCells: metrics.l2Count + metrics.l3Count + metrics.l4Count,
                l3OrAboveRequiredCells: metrics.l3Count + metrics.l4Count,
                l4RequiredCells: metrics.l4Count,
                hardnessScore: +metrics.score.toFixed(3),
                // K-loop bookkeeping. attemptsUsed = how many carves
                // we actually ran for this puzzle (easy = 1, medium/
                // hard = the bias-driven K).
                attemptsUsed: actualK,
                startMaxK: plannedK,
                startMaxKActual: actualK,
                batchBias: batchBias == null ? null : +batchBias.toFixed(3),
                startMaxPasses: carveStats.passes,
                startMaxAttempts: carveStats.attempts,
                startMaxCellRemoves: carveStats.cellsRemoved,
                startMaxWallRemoves: carveStats.wallsRemoved,
                weightCell: carveStats.weightCell,
                weightWall: carveStats.weightWall,
            },
        };
        puzzle.stats.verified = verifySolvable(filled, walls, solution, N, params.tactics);
        return puzzle;
    }

    // How many of the *last* successful removals an easy carve
    // rolls back. Larger N → more rollbacks so the absolute amount
    // of "extra help" scales with the board.
    function easyBackfillCount(N) {
        return Math.max(2, Math.floor(N / 2));
    }

    // Generate a puzzle by running the start-from-max carve on the
    // sampled `solution`. Calls
    //   await onProgress(fraction /* 0..1 */)
    // after each completed carve so the UI can drive a determinate
    // bar.
    //
    // Branch behaviour
    // ----------------
    //   Easy
    //     Single carve. (wCell, wWall) are anchored at the natural
    //     cell/wall count ratio with ±50% jitter so each New Game
    //     still feels different. After the carve hits its
    //     can't-remove-anything fixed point we restore the last
    //     `easyBackfillCount(N)` removals so the player gets back a
    //     chunk of the "hardest" constraints that would otherwise
    //     have been carved away.
    //   Medium / Hard
    //     Pick the batch-level cell/wall preference once via
    //     `batchBias ∈ U(0, 1)`. Every K-carve in this batch reuses
    //     the same (wCell, wWall) = (2·bias, 2·(1−bias)); within-
    //     batch variation comes from the per-candidate noise. Among
    //     the K carves we pick the highest-scoring one (the
    //     "hardest available within this bias").
    //
    //     K is non-linear in bias to balance the time spent across
    //     bias regimes:
    //         K = max(2, round(K_max · ((1 − b) + 0.45 · (1 − b)^2)))
    //     The (1 − b)^2 booster pushes K above K_max in the prefill-
    //     favouring half (low bias produces naturally easy puzzles
    //     where more tries are useful), and the floor of 2 keeps
    //     the wall-favouring tail honest — we always pick the
    //     better of at least two carves. Expected E[K] ≈ 0.65·K_max,
    //     ~30% more attempts than a pure linear schedule.
    async function generateFromMaxOnSolution(N, difficulty, seed, solution, params, onProgress) {
        const masterRng = PC.rng.make(seed);
        const weights = tierWeights(N);
        const breakdown = buildTierBreakdown(N, params.tactics);
        const scoreOf = (filled, walls) => {
            const b = breakdown(filled, walls);
            return { ...b, score: tierScore(b, weights) };
        };

        // ---- Easy: 1 carve + back-fill ----
        if (difficulty === 'easy') {
            const cellCount = N * N;
            const wallCount = 2 * N * (N - 1);
            const wAvg = 2 / (cellCount + wallCount);
            // Per-carve anchor at the natural count ratio; the
            // ±50% jitter still injects variation between New Game
            // presses.
            const wCell = cellCount * wAvg * (0.5 + masterRng());
            const wWall = wallCount * wAvg * (0.5 + masterRng());
            const carveRng = PC.rng.make((seed ^ 0x9e3779b9) >>> 0);

            const carve = carveFromMaxOnce(N, params, solution, carveRng, wCell, wWall);

            // Roll back the last few removals. These are the
            // constraints the carve dropped *latest*, i.e. the
            // most "essential" ones (everything earlier survived
            // verifySolvable just fine). Putting them back makes
            // the puzzle easier without invalidating it.
            const backfill = Math.min(easyBackfillCount(N), carve.removalLog.length);
            let cellsBackfilled = 0;
            let wallsBackfilled = 0;
            for (let i = 0; i < backfill; i++) {
                const item = carve.removalLog.pop();
                if (item.kind === 'cell') {
                    carve.filled[item.r][item.c] = solution[item.r][item.c];
                    carve.stats.cellsRemoved--;
                    cellsBackfilled++;
                } else {
                    carve.walls.push(item.wall);
                    carve.stats.wallsRemoved--;
                    wallsBackfilled++;
                }
            }
            carve.stats.easyBackfill = backfill;
            carve.stats.easyBackfillCells = cellsBackfilled;
            carve.stats.easyBackfillWalls = wallsBackfilled;

            if (onProgress) await onProgress(1);

            const m = scoreOf(carve.filled, carve.walls);
            return buildPuzzleFromCarve(N, difficulty, seed, solution, params,
                carve, m, 1, 1, null);
        }

        // ---- Medium / Hard: batch-bias-driven K-loop ----
        const batchBias = masterRng();           // U(0, 1)
        // batchBias = 1 → wCell maximal, wWall ≈ 0 → cells get
        //                 removed first → wall-heavy puzzle (hard)
        // batchBias = 0 → wWall maximal, wCell ≈ 0 → walls get
        //                 removed first → cell-heavy puzzle (easy)
        // batchBias = cellShare → matches the natural count anchor.
        const wCell = batchBias * 2;
        const wWall = (1 - batchBias) * 2;

        const Kmax = startFromMaxBudget(N, difficulty);
        // Non-linear K schedule with floor = 2.
        //
        //   K = Kmax * ( (1-bias) + 0.45 * (1-bias)^2 )
        //
        // The first term is the original linear schedule; the
        // (1-bias)^2 booster only kicks in meaningfully at low
        // bias (prefill-favouring half), where it pushes K above
        // Kmax — at bias=0 we run ~1.45*Kmax carves to dig out a
        // hard puzzle, while the wall-favouring tail relaxes onto
        // the floor of 2. The integral of the booster is 0.45/3 =
        // 0.15, so overall E[K] ≈ 0.65*Kmax, ~30% more attempts
        // than the linear (E[K] = 0.5*Kmax) baseline.
        const Kfloor = 2;
        const t = 1 - batchBias;
        const K = Math.max(Kfloor, Math.round(Kmax * (t + 0.45 * t * t)));

        let best = null;
        let bestScore = -Infinity;
        for (let k = 0; k < K; k++) {
            const attemptSeed = (seed ^ ((k + 1) * 0x9e3779b9)) >>> 0;
            const attemptRng = PC.rng.make(attemptSeed);
            const carve = carveFromMaxOnce(N, params, solution, attemptRng, wCell, wWall);
            const m = scoreOf(carve.filled, carve.walls);
            if (m.score > bestScore) {
                bestScore = m.score;
                best = { ...carve, metrics: m };
            }
            if (onProgress) {
                await onProgress((k + 1) / K);
            }
        }

        return buildPuzzleFromCarve(N, difficulty, seed, solution, params,
            best, best.metrics, Kmax, K, batchBias);
    }

    async function generateOnce(size, difficulty, seed, onProgress) {
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
        return await generateFromMaxOnSolution(N, difficulty, seed,
            solution, params, onProgress);
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
    // Enumerate every deduction at the lowest tier that has any. The
    // hint UI uses this so it can rank multiple equally-easy choices
    // by player-continuity heuristics (which `nextDeduction` can't do
    // because it short-circuits on the first hit).
    //
    // Output:
    //   { tier: 'L1'..'L4',
    //     deductions: [{ tier, cell:[r,c], value, reason }, ...] }
    //   or null if no tactic in `tactics` finds anything.
    // -----------------------------------------------------------------

    function findLowestAvailableTier(filled, walls, N, tactics) {
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
            const out = [];
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (filled[r][c] !== 0) continue;
                    const e = fn(r, c, filled, wallIndex, N);
                    if (e) out.push({ tier, cell: [r, c], value: e.value, reason: e.reason });
                }
            }
            if (out.length > 0) return { tier, deductions: out };
        }
        return null;
    }

    // -----------------------------------------------------------------
    // Natural-language descriptions of L1 reasons and contradictions.
    // Used by both the in-game hint UI and the debug trace tool, so the
    // wording stays in sync.
    // -----------------------------------------------------------------

    function symbolText(v) { return v === SUN ? '☀' : '☾'; }
    function cellText([r, c]) { return `(${r}, ${c})`; }

    /**
     * Hint-text dictionary. English is the active locale (see
     * `PuzzleCommon.i18n.locale`); Chinese strings are kept here too
     * so a future UI toggle can switch back without re-translating.
     * Both locales receive the same pre-rendered symbol glyphs (☀/☾)
     * and wall glyphs (=/×), which read the same in any language.
     */
    const HINT_TEXTS = {
        en: {
            rowName: 'row',
            colName: 'column',
            tCount: (orient, full, val) =>
                `Half this ${orient} is already ${full}, so the yellow cell is ${val}.`,
            tThree: (orient, src, val) =>
                `${src} in the yellow cell makes three ${src} in this ${orient}, so it's ${val}.`,
            tWall: (wall, neighbor, val) =>
                `Across the ${wall} wall is ${neighbor}, so the yellow cell is ${val}.`,
            lAssume: (hypVal, tail, val) =>
                `If the yellow cell were ${hypVal}: ${tail} (red). So it's ${val}.`,
            cCountOverflow: (orient, val) =>
                `too many ${val} in a ${orient}`,
            cThreeInRow: (val) =>
                `three ${val} in a row`,
            cWall: (wall) =>
                `the ${wall} wall would break`,
            cDefault: () => 'a rule violation',
        },
        zh: {
            rowName: '列',
            colName: '行',
            tCount: (orient, full, val) =>
                `這一${orient}的 ${full} 已經放滿一半，所以黃底這格必須是 ${val}。`,
            tThree: (orient, src, val) =>
                `若黃底這格放 ${src}，這一${orient}就會出現連續三個 ${src}，所以它必須是 ${val}。`,
            tWall: (wall, neighbor, val) =>
                `${wall} 牆對面的格子是 ${neighbor}，所以黃底這格必須是 ${val}。`,
            lAssume: (hypVal, tail, val) =>
                `假設黃底這格是 ${hypVal}，會逼得 ${tail}（紅色推論），所以它只能是 ${val}。`,
            cCountOverflow: (orient, val) =>
                `這一${orient}的 ${val} 超過一半`,
            cThreeInRow: (val) =>
                `連續三格都是 ${val}`,
            cWall: (wall) =>
                `${wall} 牆兩側不符規則`,
            cDefault: () => '違反規則',
        },
    };

    function currentTexts() {
        const loc = (global.PuzzleCommon && global.PuzzleCommon.i18n
            && global.PuzzleCommon.i18n.locale) || 'en';
        return HINT_TEXTS[loc] || HINT_TEXTS.en;
    }

    /**
     * Player-facing brief description of a contradiction. Avoids
     * coordinates (the board itself highlights the cells in red)
     * and avoids "L1/L2/L3/L4" / "step count" jargon.
     */
    function describeContradictionBrief(c) {
        const t = currentTexts();
        if (c.kind === 'count-overflow') {
            const orient = c.orientation === 'row' ? t.rowName : t.colName;
            return t.cCountOverflow(orient, symbolText(c.value));
        }
        if (c.kind === 'three-in-row') {
            return t.cThreeInRow(symbolText(c.value));
        }
        if (c.kind === 'wall') {
            const wall = c.wallKind === 'same' ? '=' : '×';
            return t.cWall(wall);
        }
        return t.cDefault();
    }

    /**
     * Player-facing description of a deduction. The hint UI marks
     * cells on the board so the prose stays jargon-free: no tier
     * names, no chain-length counts. The board provides the "where",
     * the prose provides the "why".
     */
    function describeReason(reason) {
        const t = currentTexts();
        if (reason.kind === 'T-count') {
            const orient = reason.orientation === 'row' ? t.rowName : t.colName;
            return t.tCount(orient, symbolText(reason.fullValue), symbolText(reason.value));
        }
        if (reason.kind === 'T-three') {
            const orient = reason.orientation === 'row' ? t.rowName : t.colName;
            return t.tThree(orient, symbolText(reason.sourceValue), symbolText(reason.value));
        }
        if (reason.kind === 'T-wall') {
            const wall = reason.wallKind === 'same' ? '=' : '×';
            return t.tWall(wall, symbolText(reason.neighborValue), symbolText(reason.value));
        }
        if (reason.kind === 'L2' || reason.kind === 'L3' || reason.kind === 'L4') {
            const tail = describeContradictionBrief(reason.contradiction);
            return t.lAssume(symbolText(reason.hypothesis.value), tail, symbolText(reason.value));
        }
        return JSON.stringify(reason);
    }

    /**
     * Supporting cells the hint UI should soft-highlight (yellow).
     * - For L1 reasons: the cells whose values are directly cited
     *   (T-count's same-color line cells, T-three's two siblings,
     *   T-wall's wall neighbour).
     * - For L2/L3/L4: the propagation chain that follows from the
     *   bad hypothesis, excluding the final-contradiction cells
     *   (those go to violationCells).
     */
    function reasonContextCells(reason) {
        if (reason.kind === 'T-count') return reason.sources || [];
        if (reason.kind === 'T-three') return reason.sources || [];
        if (reason.kind === 'T-wall') return [reason.neighbor];
        if (reason.kind === 'L2' || reason.kind === 'L3' || reason.kind === 'L4') {
            return (reason.propagation || []).map((s) => s.cell);
        }
        return [];
    }

    /**
     * Cells where the actual rule violation happens — only meaningful
     * for L2/L3/L4 deductions. The hint UI paints these red so the
     * player sees exactly *what* breaks if they pick the bad value.
     */
    function reasonViolationCells(reason) {
        if (reason.kind === 'L2' || reason.kind === 'L3' || reason.kind === 'L4') {
            return (reason.contradiction && reason.contradiction.cells) || [];
        }
        return [];
    }

    /**
     * Intermediate placements forced by the bad hypothesis. The hint
     * UI overlays these as faded "ghost" symbols so the player can
     * follow the contradiction chain visually. Includes the hypothesis
     * cell itself (the player needs to see the assumed value on the
     * target cell, not just "if X is something"). Empty for L1.
     */
    function reasonChainPlacements(reason) {
        if (reason.kind === 'L2' || reason.kind === 'L3' || reason.kind === 'L4') {
            const out = [];
            if (reason.hypothesis && reason.hypothesis.cell) {
                out.push({ cell: reason.hypothesis.cell, value: reason.hypothesis.value });
            }
            for (const s of (reason.propagation || [])) {
                out.push({ cell: s.cell, value: s.value });
            }
            return out;
        }
        return [];
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.tango = generate;
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleSolvers.tango = {
        nextDeduction,
        findLowestAvailableTier,
        describeReason,
        describeContradictionBrief,
        reasonContextCells,
        reasonViolationCells,
        reasonChainPlacements,
        buildWallIndex,
        SUN, MOON,
    };
})(window);
