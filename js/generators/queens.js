/**
 * Queens puzzle generator — region-expansion under tactic-bounded
 * unique-solution verification.
 *
 * High-level strategy (MVP — single-shot, no scoring, no K-batching)
 * ------------------------------------------------------------------
 *   1. Place N non-attacking queens (one per row/col, no two 8-adjacent).
 *   2. Initialise each queen as a singleton region — every other cell
 *      starts unassigned (regions[r][c] === -1, candidate[r][c] === false).
 *   3. DFS-expand into all unassigned cells: at each step pick the most
 *      constrained frontier cell (unassigned + 4-adjacent to ≥1 already
 *      assigned region; chosen by fewest viable adjacent regions = MRV)
 *      and try each adjacent region in random order. After every
 *      tentative assignment we re-run the tactic-bounded solver against
 *      the *current partial* board; if it still places all N queens we
 *      recurse, otherwise we revert and try the next region. Standard
 *      DFS backtracking, no pruning beyond MRV.
 *   4. When every cell is assigned we have a complete puzzle whose
 *      unique solution is provably reachable under the chosen tier.
 *   5. The whole search runs under a wall-clock deadline; on timeout
 *      we bail this attempt and try the next seed. Up to 10 retries
 *      before giving up.
 *
 * Tactic tiers
 * ------------
 *   T1 — queen kills neighbours / row / col / region (implicit on placement)
 *   T2 — naked single in a row / col / region
 *   T3 — pigeonhole on K regions × K rows / cols
 *   T4 — covering using ONLY geometric kills (row / col / 8-neighbour)
 *   T5 — covering that additionally relies on same-region kills
 *
 *   easy   — T1 + T2
 *   medium — easy + T3 + T4
 *   hard   — medium + T5
 *
 * T3 and T4 are treated as equal difficulty by the difficulty mapping
 * (both flip on at medium). The solver still has a deterministic
 * order — T2 → T4 → T3 → T5 — because T4-tried-before-T3 surfaces
 * cleaner per-region hints when a region's candidates are confined to
 * a single row or column (T4 catches the row/col kills AND the
 * 8-adjacent neighbours; T3 only catches the row/col kills, folded
 * across multiple regions). Cases that genuinely need K-region
 * pigeonhole still fall through to T3.
 *
 * All covering steps batch every cell their group excludes into one
 * step, so the player reads one hint per (group, deduction) pair
 * instead of N hints with identical group framing.
 *
 * MVP scope intentionally omits:
 *   - K-attempt batching + best-of-K scoring
 *   - Weighted hardness score / dynamic L4-style weighting
 *   - Difficulty-aware simplification (Tango's wall-absorb pass)
 *   - Stats infrastructure for empirical tuning
 * Once we can produce *any* legitimate puzzle at each tier we'll layer
 * those back on the way we did for Tango.
 *
 * Partial-board solver semantics
 * ------------------------------
 * The solver treats `regions[r][c] === -1` as "this cell is not in any
 * region", which means it is not a candidate for being a queen of any
 * region/row/col. Initially only the N queen cells are candidates, so
 * T2 (naked single) immediately places all N queens — uniqueness
 * trivially holds. As expansion proceeds more cells become candidates
 * and uniqueness can break, at which point the solver will fail to
 * place all N queens and the DFS will revert that assignment.
 *
 * Debug logging
 * -------------
 * Pass `?queens_debug=1` in the URL to get per-attempt console output
 * (DFS steps, retries, timing, why a seed bailed).
 */

(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    const DEBUG = (function () {
        try {
            return new URL(location.href).searchParams.get('queens_debug') === '1';
        } catch (e) {
            return false;
        }
    })();
    const dbg = DEBUG ? console.log.bind(console, '[queens-gen]') : () => {};

    // -----------------------------------------------------------------
    // Tactic tiers
    // -----------------------------------------------------------------

    // Tier roster:
    //   T1 — queen kills (placement consequence, always implicit)
    //   T2 — naked single in a row / col / region
    //   T3 — pigeonhole on K regions × K rows / cols
    //   T4 — covering using ONLY geometric kills (row / col / 8-neighbour)
    //   T5 — covering that additionally relies on same-region kills
    //
    // Difficulty mapping treats T3 and T4 as equal weight (both flip on
    // at medium). The solver's tactic ordering (defined in
    // `solveWithTactics`) is T2 → T4 → T3 → T5 — see that comment for
    // why T4 is tried before T3 despite the equal-difficulty framing.
    //
    // T4 + T5 are the "covering" family split: requiring the player to
    // also track region colors makes the same-region variant materially
    // harder than the pure-geometric one. T5 only emits when at least
    // one same-region kill is *necessary*, so geometric-only cases are
    // always reported under T4.
    const TACTICS_BY_DIFFICULTY = {
        easy:   { T1: true, T2: true,  T3: false, T4: false, T5: false },
        medium: { T1: true, T2: true,  T3: true,  T4: true,  T5: false },
        hard:   { T1: true, T2: true,  T3: true,  T4: true,  T5: true  },
    };

    // Per-N wall-clock deadlines for one expand-DFS attempt. Sized to
    // be comfortably above what an unconstrained search needs in the
    // common case; the user explicitly asked for "full firepower" with
    // these only acting as the safety fuse.
    function attemptTimeoutMs(N) {
        if (N <= 6) return 10000;
        if (N <= 8) return 30000;
        if (N <= 10) return 90000;
        return 150000;
    }

    // Per-(N, difficulty) hard cap on how many seeds we're willing to
    // burn before giving up on generation. Always ≥ candidateBudget
    // with a few extra slots for failed / timed-out expansions so
    // the pool sampling isn't starved on unlucky seeds. Small boards
    // can afford a much bigger cap because each expansion finishes
    // in a fraction of a second.
    function maxSeedRetries(N, difficulty) {
        const budget = candidateBudget(N, difficulty);
        // 4 failed-seed slack for large boards, 6 for small.
        const slack = N <= 6 ? 6 : 4;
        return Math.max(10, budget + slack);
    }

    // Per-(N, difficulty) "quality" targets applied to expanded
    // puzzles. Two axes, both caps on how many cheap regions we
    // tolerate:
    //   maxSingletonRegions - regions of size 1. Free naked-single
    //     hint (score 1), player barely thinks.
    //   maxTinyRegions      - regions of size ≤ 2. A size-2 region
    //     usually collapses immediately via T4-line-contiguous
    //     (score 3) or by having its second candidate killed by
    //     another queen's t1 — either way it plays as free progress.
    //     A "tiny" count also includes singletons, so this is the
    //     broader dimension.
    // Easy imposes no cap on either — the point of easy is plenty
    // of anchors. Medium / hard tighten both.
    function qualityTargets(N, difficulty) {
        if (difficulty === 'hard') {
            return { maxSingletonRegions: 0, maxTinyRegions: 1 };
        }
        if (difficulty === 'medium') {
            return {
                maxSingletonRegions: 1,
                maxTinyRegions: Math.max(1, Math.floor(N / 4)),
            };
        }
        return { maxSingletonRegions: Infinity, maxTinyRegions: Infinity };
    }

    function meetsQuality(stats, quality) {
        return stats.singletonRegions <= quality.maxSingletonRegions
            && stats.tinyRegions <= quality.maxTinyRegions;
    }

    // How many quality-passing candidate puzzles to collect before
    // picking the hardest one. Mirrors Tango's "generate K, pick
    // best" approach: more samples → better shot at hitting the top
    // of the difficulty band, at the cost of wall time.
    //
    // Flat across board size (the user found even N=12 generation
    // fast enough at these counts, and larger boards actually have
    // MORE headroom for hard deductions, so there's no reason to
    // starve them of samples). Scaled only by difficulty:
    //   * Easy short-circuits to 1 — the point of easy is to be
    //     quick + gentle, no reason to hunt for the "hardest easy".
    //   * Medium / hard sample a big pool so the picker can reject
    //     the "too easy" layouts a random draw still produces.
    // Note this is the OUTER budget; each seed also yields up to
    // innerSearchDepth layouts, so the real pool the picker sees is
    // larger than this number.
    function candidateBudget(N, difficulty) {
        if (difficulty === 'easy') return 1;
        if (difficulty === 'medium') return 16;
        return 36; // hard
    }

    // Inner search depth for expandRegions — after finding the first
    // valid layout for a given queens placement, keep the DFS running
    // past the base case and collect up to this many layouts total.
    // Each additional layout shares most of the "forced corridor"
    // work already spent, so the extra cost per layout is much
    // cheaper than starting a fresh seed. Amplifies the candidate
    // pool by roughly this factor without extra placeQueens calls.
    function innerSearchDepth(N, difficulty) {
        if (difficulty === 'easy') return 1;
        if (difficulty === 'medium') return 2;
        return 3;
    }

    // Rank two candidates for "which is a better puzzle at this
    // difficulty". Higher is better on the primary axis; ties fall
    // through in order:
    //   1. Meets quality (singletons AND tinies ≤ target)  boolean
    //   2. sumScore                                        total effort
    //   3. peakScore                                       hardest step
    //   4. fewer tiny regions                              visual polish
    //   5. fewer singleton regions                         tie-break
    // Returns negative if `a` is better, positive if `b` is better.
    function compareCandidates(a, b, quality) {
        const aQ = meetsQuality(a.stats, quality) ? 1 : 0;
        const bQ = meetsQuality(b.stats, quality) ? 1 : 0;
        if (aQ !== bQ) return bQ - aQ;
        if (a.stats.sumScore !== b.stats.sumScore) {
            return b.stats.sumScore - a.stats.sumScore;
        }
        if (a.stats.peakScore !== b.stats.peakScore) {
            return b.stats.peakScore - a.stats.peakScore;
        }
        if (a.stats.tinyRegions !== b.stats.tinyRegions) {
            return a.stats.tinyRegions - b.stats.tinyRegions;
        }
        return a.stats.singletonRegions - b.stats.singletonRegions;
    }

    // -----------------------------------------------------------------
    // Queens placement — shuffled DFS, one queen per row.
    //
    // The 8-adjacency rule combined with one-per-col reduces to
    // |cols[r] - cols[r-1]| > 1, which is what the candidate filter
    // below enforces row by row.
    // -----------------------------------------------------------------

    function placeQueens(N, rng) {
        const cols = new Array(N).fill(-1);
        const used = new Array(N).fill(false);

        function solve(row) {
            if (row === N) return true;
            const cands = [];
            for (let c = 0; c < N; c++) {
                if (used[c]) continue;
                if (row > 0 && Math.abs(c - cols[row - 1]) <= 1) continue;
                cands.push(c);
            }
            PC.rng.shuffle(cands, rng);
            for (const c of cands) {
                cols[row] = c;
                used[c] = true;
                if (solve(row + 1)) return true;
                used[c] = false;
            }
            cols[row] = -1;
            return false;
        }

        return solve(0) ? cols.slice() : null;
    }

    // -----------------------------------------------------------------
    // Solver primitives
    //
    // State shape:
    //   N              — board side
    //   regions        — int[N][N], -1 for unassigned cells
    //   candidate      — bool[N][N], live "could still be a queen here"
    //   placed         — bool[N][N], committed queen cells
    //   placedCount    — number of committed queens (== solver placedCount)
    //   regionCells    — int[N][][] precomputed cells per region id
    //
    // The solver applies T1 implicitly whenever it calls `placeAt`,
    // then loops T2 → T4 → T3 → T5 (subject to the tactics mask)
    // until no tactic makes progress. See `solveWithTactics` for why
    // T4 is tried before T3 even though they share a difficulty tier.
    // -----------------------------------------------------------------

    function buildRegionCells(regions, N) {
        const out = Array.from({ length: N }, () => []);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const k = regions[r][c];
                if (k !== -1) out[k].push([r, c]);
            }
        }
        return out;
    }

    function makeSolverState(regions, N) {
        const candidate = Array.from({ length: N }, () => new Array(N).fill(false));
        const placed = Array.from({ length: N }, () => new Array(N).fill(false));
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (regions[r][c] !== -1) candidate[r][c] = true;
            }
        }
        return {
            N, regions, candidate, placed,
            placedCount: 0,
            regionCells: buildRegionCells(regions, N),
        };
    }

    // Queen at (r1, c1) kills cell (r2, c2) (i.e. (r2, c2) cannot be
    // another queen) iff they share a row, column, region, or are
    // 8-adjacent. The cell itself is not "killed" by the placed queen.
    function killsBetween(state, r1, c1, r2, c2) {
        if (r1 === r2 && c1 === c2) return false;
        if (r1 === r2) return true;
        if (c1 === c2) return true;
        if (Math.abs(r1 - r2) <= 1 && Math.abs(c1 - c2) <= 1) return true;
        const rg1 = state.regions[r1][c1];
        const rg2 = state.regions[r2][c2];
        if (rg1 !== -1 && rg1 === rg2) return true;
        return false;
    }

    // Geometric subset of killsBetween — same row / col / 8-neighbour,
    // intentionally ignoring the same-region rule. Used by the easier
    // T4 tier so the player doesn't also have to track region colors
    // when reading the hint.
    function killsGeom(r1, c1, r2, c2) {
        if (r1 === r2 && c1 === c2) return false;
        if (r1 === r2) return true;
        if (c1 === c2) return true;
        if (Math.abs(r1 - r2) <= 1 && Math.abs(c1 - c2) <= 1) return true;
        return false;
    }

    // Commit (r, c) as a queen and run T1 propagation: every candidate
    // cell that conflicts with the placed queen is excluded. Returns
    // the list of cells T1 just killed so callers (the trace tool and
    // eventually the hint UI) can surface a separate "T1: queen at
    // (r,c) kills these cells" step.
    function placeAt(state, r, c) {
        if (state.placed[r][c]) return [];
        state.placed[r][c] = true;
        state.placedCount += 1;
        state.candidate[r][c] = false;
        const { N, candidate } = state;
        const killed = [];
        for (let r2 = 0; r2 < N; r2++) {
            for (let c2 = 0; c2 < N; c2++) {
                if (!candidate[r2][c2]) continue;
                if (killsBetween(state, r, c, r2, c2)) {
                    candidate[r2][c2] = false;
                    killed.push([r2, c2]);
                }
            }
        }
        return killed;
    }

    function excludeAt(state, r, c) {
        state.candidate[r][c] = false;
    }

    // Snapshot a list of cells in a constraint group — used by the
    // step explanations to populate `groupCells` (the cells the hint
    // UI highlights in yellow) and `groupCandidates` (the subset
    // still in play, which T2 / T4 / T5 actually reason about).
    function rowCells(N, r) {
        const out = [];
        for (let c = 0; c < N; c++) out.push([r, c]);
        return out;
    }
    function colCells(N, c) {
        const out = [];
        for (let r = 0; r < N; r++) out.push([r, c]);
        return out;
    }

    // T2 — naked single in any row / column / region. Returns a step
    // object describing the placement (including the T1 cascade it
    // immediately triggers) or null when no group has exactly one
    // candidate.
    //
    // Step shape:
    //   { tier: 'T2',
    //     groupKind: 'row'|'col'|'region',
    //     groupIndex,                    // r, c, or region id
    //     groupCells:    [[r,c], ...],   // all cells of the group
    //     placedAt:      [r, c],
    //     t1Killed:      [[r,c], ...] }  // cells T1 just excluded
    function stepT2(state) {
        const { N, candidate, placed, regionCells } = state;

        // Rows
        for (let r = 0; r < N; r++) {
            let count = 0, lastC = -1;
            for (let c = 0; c < N; c++) {
                if (candidate[r][c]) { count++; lastC = c; if (count > 1) break; }
            }
            if (count === 1 && !placed[r][lastC]) {
                const killed = placeAt(state, r, lastC);
                dbg('T2 row', r, '→', lastC, 'killed', killed.length);
                return {
                    tier: 'T2',
                    groupKind: 'row',
                    groupIndex: r,
                    groupCells: rowCells(N, r),
                    placedAt: [r, lastC],
                    t1Killed: killed,
                };
            }
        }
        // Cols
        for (let c = 0; c < N; c++) {
            let count = 0, lastR = -1;
            for (let r = 0; r < N; r++) {
                if (candidate[r][c]) { count++; lastR = r; if (count > 1) break; }
            }
            if (count === 1 && !placed[lastR][c]) {
                const killed = placeAt(state, lastR, c);
                dbg('T2 col', c, '→', lastR, 'killed', killed.length);
                return {
                    tier: 'T2',
                    groupKind: 'col',
                    groupIndex: c,
                    groupCells: colCells(N, c),
                    placedAt: [lastR, c],
                    t1Killed: killed,
                };
            }
        }
        // Regions
        for (let k = 0; k < N; k++) {
            let count = 0, lastR = -1, lastC = -1;
            for (const cell of regionCells[k]) {
                const r = cell[0], c = cell[1];
                if (candidate[r][c]) { count++; lastR = r; lastC = c; if (count > 1) break; }
            }
            if (count === 1 && !placed[lastR][lastC]) {
                const killed = placeAt(state, lastR, lastC);
                dbg('T2 region', k, '→', lastR, lastC, 'killed', killed.length);
                return {
                    tier: 'T2',
                    groupKind: 'region',
                    groupIndex: k,
                    groupCells: regionCells[k].slice(),
                    placedAt: [lastR, lastC],
                    t1Killed: killed,
                };
            }
        }
        return null;
    }

    // T3 — pigeonhole on regions × rows and regions × cols.
    //
    // For every subset S of regions with 2 ≤ |S| ≤ N-1:
    //   • Compute rowUnion = ⋃ regionRows(k) for k in S.
    //   • Because S's |S| queens must sit in |S| distinct rows AND
    //     each must come from one of S's candidates, |rowUnion| ≥ |S|.
    //     If |rowUnion| === |S|, those |S| rows are reserved for S's
    //     queens — every candidate in those rows whose region is NOT
    //     in S can be excluded.
    //   • Same logic for columns.
    //
    // We enumerate subsets ordered by popcount (smaller first) so the
    // hint UI tends to surface the most-readable pigeonhole — fewer
    // regions = fewer cells the player needs to track. Exits on the
    // first useful exclusion so each step stays small.
    //
    // Step shape:
    //   { tier: 'T3',
    //     axis: 'row'|'col',
    //     regionIds:        [int, ...],   // |S| regions involved
    //     reservedAxis:     [int, ...],   // |S| rows or cols reserved
    //     regionCandidates: [[r,c], ...], // candidates inside the regions
    //     excludedAt:       [[r,c], ...]} // cells we just excluded
    function stepT3(state) {
        const { N, candidate, regions, regionCells } = state;

        const regionRows = new Array(N);
        const regionCols = new Array(N);
        const regionCands = new Array(N);
        for (let k = 0; k < N; k++) {
            const rs = new Set();
            const cs = new Set();
            const cands = [];
            for (const [r, c] of regionCells[k]) {
                if (candidate[r][c]) {
                    rs.add(r); cs.add(c);
                    cands.push([r, c]);
                }
            }
            regionRows[k] = rs;
            regionCols[k] = cs;
            regionCands[k] = cands;
        }

        // Enumerate masks ordered by popcount (2, then 3, ...). For N up
        // to 12 this is at most ~4K masks; a one-shot precompute keeps
        // the hot loop tight.
        const masks = [];
        const total = 1 << N;
        for (let mask = 1; mask < total; mask++) {
            const k = popcount(mask);
            if (k >= 2 && k < N) masks.push({ mask, k });
        }
        masks.sort((a, b) => a.k - b.k || a.mask - b.mask);

        for (const { mask, k } of masks) {
            let hasEmpty = false;
            const rowUnion = new Set();
            const colUnion = new Set();
            const regionIds = [];
            const allCands = [];
            for (let i = 0; i < N; i++) {
                if ((mask & (1 << i)) === 0) continue;
                if (regionRows[i].size === 0) { hasEmpty = true; break; }
                regionIds.push(i);
                for (const r of regionRows[i]) rowUnion.add(r);
                for (const c of regionCols[i]) colUnion.add(c);
                for (const cell of regionCands[i]) allCands.push(cell);
            }
            if (hasEmpty) continue;

            if (rowUnion.size === k) {
                const excluded = [];
                for (const r of rowUnion) {
                    for (let c = 0; c < N; c++) {
                        if (!candidate[r][c]) continue;
                        const reg = regions[r][c];
                        if (reg === -1) continue;
                        if ((mask & (1 << reg)) === 0) {
                            excludeAt(state, r, c);
                            excluded.push([r, c]);
                            dbg('T3-row exclude', r, c, 'mask', mask.toString(2));
                        }
                    }
                }
                if (excluded.length) {
                    return {
                        tier: 'T3',
                        axis: 'row',
                        regionIds,
                        reservedAxis: Array.from(rowUnion).sort((a, b) => a - b),
                        regionCandidates: allCands,
                        excludedAt: excluded,
                    };
                }
            }
            if (colUnion.size === k) {
                const excluded = [];
                for (const c of colUnion) {
                    for (let r = 0; r < N; r++) {
                        if (!candidate[r][c]) continue;
                        const reg = regions[r][c];
                        if (reg === -1) continue;
                        if ((mask & (1 << reg)) === 0) {
                            excludeAt(state, r, c);
                            excluded.push([r, c]);
                            dbg('T3-col exclude', r, c, 'mask', mask.toString(2));
                        }
                    }
                }
                if (excluded.length) {
                    return {
                        tier: 'T3',
                        axis: 'col',
                        regionIds,
                        reservedAxis: Array.from(colUnion).sort((a, b) => a - b),
                        regionCandidates: allCands,
                        excludedAt: excluded,
                    };
                }
            }
        }
        return null;
    }

    function popcount(x) {
        let n = 0;
        while (x) { n += x & 1; x >>>= 1; }
        return n;
    }

    // T4 / T5 — covering. For some constraint group G with ≥2 candidates,
    // find every candidate cell x outside G that is killed by every
    // candidate of G. Such an x cannot be a queen (whichever cand of G
    // wins, x dies), so we exclude it. All exclusions found from the
    // SAME group are batched into a single step so the player only
    // needs to read "this {row/col/region} forces these cells out" once.
    //
    // The covering family is split by which kill-rule the deduction
    // requires:
    //   T4 — only geometric kills (row / col / 8-neighbour)
    //   T5 — at least one same-region kill is required
    //
    // T4 is the easier hint to read because the player doesn't also
    // have to track region colors. The solver runs T4 before T5, and
    // stepT5 only emits if at least one candidate's kill on each
    // excluded cell is region-only (i.e. not reachable via geometry
    // alone). That guarantees a T5 hint genuinely requires the
    // region-color framing.
    //
    // Step shape (excludedAt is always an array — possibly length 1):
    //   { tier: 'T4' | 'T5',
    //     groupKind: 'row'|'col'|'region',
    //     groupIndex,
    //     groupCells:        [[r,c], ...],
    //     groupCandidates:   [[r,c], ...],   // the actual blockers
    //     regionKillers:     [[r,c], ...],   // (T5 only) union of cands that needed region-kill
    //     excludedAt:        [[r,c], ...] }  // every cell this step excludes
    function stepCoverInner(state, killsFn, tierLabel, requireRegionKill) {
        const { N, candidate, regions, regionCells } = state;

        const tryGroup = (groupKind, groupIndex, cells, isInGroup) => {
            const cands = [];
            for (const [r, c] of cells) {
                if (candidate[r][c]) cands.push([r, c]);
            }
            if (cands.length < 2) return null;

            const excluded = [];
            const rkSet = new Set();   // cand index → seen
            const rkList = [];         // dedup'd union of region-killer candidates

            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (!candidate[r][c]) continue;
                    if (isInGroup(r, c)) continue;
                    let allKill = true;
                    const localRk = [];
                    for (let i = 0; i < cands.length; i++) {
                        const cand = cands[i];
                        if (!killsFn(state, cand[0], cand[1], r, c)) {
                            allKill = false;
                            break;
                        }
                        if (requireRegionKill
                            && !killsGeom(cand[0], cand[1], r, c)) {
                            localRk.push(i);
                        }
                    }
                    if (!allKill) continue;
                    if (requireRegionKill && localRk.length === 0) {
                        // T5 skips anything T4 could have caught.
                        continue;
                    }
                    excluded.push([r, c]);
                    for (const i of localRk) {
                        if (!rkSet.has(i)) {
                            rkSet.add(i);
                            rkList.push(cands[i]);
                        }
                    }
                }
            }

            if (excluded.length === 0) return null;

            for (const [r, c] of excluded) excludeAt(state, r, c);
            dbg(tierLabel, 'batch exclude', excluded.length,
                'by', groupKind, groupIndex,
                'cands=', cands.length,
                'regionKillers=', rkList.length);

            return {
                tier: tierLabel,
                groupKind,
                groupIndex,
                groupCells: cells.slice(),
                groupCandidates: cands,
                regionKillers: rkList,
                excludedAt: excluded,
            };
        };

        // Iterate region groups first — when a region's candidates are
        // locked to a single row or column (the "1×N region" special
        // case), T4-on-region captures both the same-row/col kills AND
        // the 8-adjacent neighbours in one batch, which is the cleanest
        // hint to surface before falling back to row / col groups.
        //
        // Within regions we further prefer those whose remaining
        // candidates are colinear (all in one row OR one column).
        // That "1×X / X×1" shape is the easiest covering hint to read
        // — "this region's queen must live in row r, so the rest of
        // row r is impossible" — so we surface it before regions whose
        // T4 exclusions come from less obvious geometric overlaps.
        // Array.sort is stable since ES2019, so non-colinear regions
        // keep their natural index order.
        const regionOrder = [];
        for (let k = 0; k < N; k++) {
            const rs = new Set();
            const cs = new Set();
            let count = 0;
            for (const [r, c] of regionCells[k]) {
                if (candidate[r][c]) { rs.add(r); cs.add(c); count++; }
            }
            const colinear = count >= 2
                && (rs.size === 1 || cs.size === 1);
            regionOrder.push({ k, colinear });
        }
        regionOrder.sort((a, b) =>
            (b.colinear ? 1 : 0) - (a.colinear ? 1 : 0));

        for (const { k } of regionOrder) {
            const result = tryGroup('region', k, regionCells[k],
                (r2, c2) => regions[r2][c2] === k);
            if (result) return result;
        }
        // Rows
        for (let r = 0; r < N; r++) {
            const result = tryGroup('row', r, rowCells(N, r), (r2) => r2 === r);
            if (result) return result;
        }
        // Cols
        for (let c = 0; c < N; c++) {
            const result = tryGroup('col', c, colCells(N, c), (_, c2) => c2 === c);
            if (result) return result;
        }
        return null;
    }

    function stepT4(state) {
        // killsGeom ignores state; wrap to match the inner signature.
        return stepCoverInner(state,
            (_s, r1, c1, r2, c2) => killsGeom(r1, c1, r2, c2),
            'T4',
            false);
    }
    function stepT5(state) {
        return stepCoverInner(state, killsBetween, 'T5', true);
    }

    // -----------------------------------------------------------------
    // Difficulty scoring.
    //
    // scoreStep(step, regions) returns { score, kind } for a single
    // solver step. The goal is a coarse numeric handle on "how much
    // work does a human do to spot this deduction" — enough to
    //   * audit generated puzzles in the trace tool, and
    //   * (later) let the generator filter seeds into a difficulty
    //     band by summing / peaking these per-step scores.
    //
    // Scores are intentionally chunky, not psychometric:
    //   T1 → 0          Kills that follow directly from a queen
    //                   placement. Rule application, not deduction.
    //   T2 → 1          Naked single. Recognition is trivial; whatever
    //                   collapsed the group to one candidate already
    //                   paid for itself on earlier turns.
    //   T3 → 3 (K=2)    Pigeonhole. Player must union K regions and
    //         5 (K=3)   notice they only touch K rows / cols. Cost
    //         8 (K≥4)   scales with K.
    //   T4 → 3 (line, contiguous)   Covering, geometric-only.
    //         4 (line, split)        The "line" case is the "1×N region
    //         6 (general)            / N×1 row/col-of-one-region" shape.
    //                   Contiguous line — the group's remaining
    //                   candidates form a solid run of cells on the
    //                   varying axis — reads instantly as "this region's
    //                   queen must live in row r, columns 2-5".
    //                   Split line — same axis but with gaps between
    //                   candidates — is subtler because the eye can't
    //                   just latch onto one continuous bar.
    //                   General case is anything else.
    //   T5 → 6 (line, contiguous)    Covering that needs region-aware
    //         7 (line, split)         kills. Same line / split /
    //         10 (general)            general classification as T4,
    //                   uniformly harder because the killer excludes
    //                   the candidate via a same-region neighbour
    //                   (extra reasoning hop).
    //
    // `regions` is optional — it lets us detect the "row/col whose
    // candidates all live in one region" flavour of the line case
    // (dual of "region whose candidates are colinear"). Omit it and
    // that flavour falls through to the general (higher) score.
    // -----------------------------------------------------------------

    function scoreStep(step, regions, context) {
        const staticScore = staticScoreStep(step, regions);
        if (!context) return staticScore;
        const boost = contextBoost(context.poolBefore, context.excludedThis,
            context.N);
        // adjusted = base + (base - 1) × boost.
        //
        // Preserves T2's static baseline of 1 no matter the context —
        // there is no such thing as a "hard naked single", the entire
        // point of T2 is that only one candidate remains. Higher tiers
        // scale up to at most 2× when boost hits 1 (dense pool with
        // stingy progress), which is roughly what the user asked for
        // with the [1, 2] multiplier option, applied only to the
        // "hardness above baseline" component.
        const base = staticScore.score;
        const adjusted = base + (base - 1) * boost;
        return {
            score: Math.round(adjusted * 100) / 100,
            kind: staticScore.kind,
            base,
            boost: Math.round(boost * 100) / 100,
        };
    }

    // The static, context-free tier score. Kept as a helper so the
    // contextual wrapper can call it once and then re-shape.
    function staticScoreStep(step, regions) {
        if (!step || !step.tier) return { score: 0, kind: 'noop' };
        switch (step.tier) {
            case 'T1': return { score: 0, kind: 'T1' };
            case 'T2': return { score: 1, kind: 'T2' };
            case 'T3': {
                const k = Array.isArray(step.regionIds)
                    ? step.regionIds.length : 2;
                if (k <= 2) return { score: 3, kind: 'T3-K2' };
                if (k === 3) return { score: 5, kind: 'T3-K3' };
                return { score: 8, kind: 'T3-Kmany' };
            }
            case 'T4':
            case 'T5': {
                const shape = coverLineShape(step, regions);
                if (step.tier === 'T4') {
                    if (!shape) return { score: 6, kind: 'T4' };
                    return shape.contiguous
                        ? { score: 3, kind: 'T4-line' }
                        : { score: 4, kind: 'T4-line-split' };
                }
                if (!shape) return { score: 10, kind: 'T5' };
                return shape.contiguous
                    ? { score: 6, kind: 'T5-line' }
                    : { score: 7, kind: 'T5-line-split' };
            }
            default:
                return { score: 0, kind: String(step.tier) };
        }
    }

    // Context boost — [0, 1] scalar summarising "how hard was the
    // player working when this step fired?". Two components:
    //   density    = poolBefore / N²
    //     Fraction of the board still in play. Early moves in a full
    //     board are harder to spot than late moves in an almost-empty
    //     one; the same T3 in state {40 candidates left} vs state {8
    //     candidates left} is really two different mental efforts.
    //   stinginess = N / (N + excludedThis)
    //     "How small was the progress?" ~1 when the step barely
    //     moved the needle (excludedThis ≤ 1), fading toward 0 as
    //     the step wipes out chunks. A puzzle where every step
    //     nibbles one cell at a time is a puzzle the player has to
    //     re-scan constantly.
    // Averaged so boost stays comfortably in [0, 1] regardless of
    // N or state.
    function contextBoost(poolBefore, excludedThis, N) {
        const density = Math.max(0, Math.min(1, poolBefore / (N * N)));
        const stinginess = N / (N + Math.max(0, excludedThis));
        return (density + stinginess) / 2;
    }

    // How many candidates a step "consumed" — cells that transitioned
    // out of the solver's candidate pool. For T2 that's the placed
    // cell itself plus its t1 kills; for T3/T4/T5 it's excludedAt.
    function progressSizeOf(step) {
        if (!step) return 0;
        if (step.tier === 'T2') {
            return 1 + (step.t1Killed ? step.t1Killed.length : 0);
        }
        return step.excludedAt ? step.excludedAt.length : 0;
    }

    // The "1×N line" special case that reads as a single-chain
    // deduction. Two symmetric flavours:
    //   * A region whose remaining candidates all sit in one row OR
    //     one column ("this region's queen must live in row r").
    //   * A row / col whose remaining candidates all belong to one
    //     region ("this row's queen must come from region k").
    //
    // Returns null if the step isn't a line at all, or
    // { contiguous: bool } describing whether the line is a solid run
    // (e.g. cols 3-6) or broken by gaps (e.g. cols 3, 5, 6). Split
    // lines are visually harder for the player to parse — the eye
    // can latch onto a solid bar much faster than onto scattered
    // cells that happen to share an axis — so scoreStep charges a
    // small premium for them.
    function coverLineShape(step, regions) {
        const cands = step.groupCandidates || [];
        if (cands.length < 2) return null;
        // Collect the coordinates along the "varying" axis of the
        // line (col if the line is a row, row if the line is a col).
        // `vals` becomes that coordinate set, or stays null if the
        // step isn't a line.
        let vals = null;
        if (step.groupKind === 'region') {
            const rs = new Set();
            const cs = new Set();
            for (const [r, c] of cands) { rs.add(r); cs.add(c); }
            if (rs.size === 1) vals = cs;
            else if (cs.size === 1) vals = rs;
        } else if ((step.groupKind === 'row' || step.groupKind === 'col')
            && regions) {
            const regs = new Set();
            for (const [r, c] of cands) {
                const reg = regions[r] ? regions[r][c] : -1;
                if (reg === -1) return null;
                regs.add(reg);
            }
            if (regs.size === 1) {
                vals = new Set();
                for (const [r, c] of cands) {
                    vals.add(step.groupKind === 'row' ? c : r);
                }
            }
        }
        if (!vals) return null;
        // Contiguous = sorted coordinates form a run with no gaps.
        // Two-candidate lines are trivially contiguous iff the two
        // coordinates differ by exactly 1.
        const sorted = Array.from(vals).sort((a, b) => a - b);
        for (let i = 1; i < sorted.length; i++) {
            if (sorted[i] - sorted[i - 1] !== 1) {
                return { contiguous: false };
            }
        }
        return { contiguous: true };
    }

    // Main solver loop — loops the allowed steps until no tactic in
    // the allowed set makes progress.
    //
    // Order: T2 → T4 → T3 → T5.
    //
    // T2 (naked single) and T5 (region-aware covering) anchor the
    // ends — easiest forced placement, hardest deduction.
    //
    // T3 (pigeonhole) and T4 (geometric covering) are treated as
    // equal difficulty by the difficulty mapping (both flip on at
    // medium). T4 is *tried first* because it gives the cleanest hint
    // for the common "a region's candidates collapse to a single row
    // or column" case: T4-on-region in one step excludes every other
    // cell of that row/col AND the 8-adjacent neighbours. T3
    // pigeonhole would catch only the row/col part, miss the 8-adj
    // part, and fold multiple regions into a single hint that's
    // harder for the player to follow.
    function solveWithTactics(regions, N, tactics) {
        const state = makeSolverState(regions, N);
        let safety = N * N * 4; // upper-bound on tactic-firings before we suspect a bug
        while (safety-- > 0) {
            if (tactics.T2 && stepT2(state)) continue;
            if (tactics.T4 && stepT4(state)) continue;
            if (tactics.T3 && stepT3(state)) continue;
            if (tactics.T5 && stepT5(state)) continue;
            break;
        }
        return state;
    }

    // True iff the tactic-bounded solver places all N queens.
    function verifyUniqueUnderTactics(regions, N, tactics) {
        const state = solveWithTactics(regions, N, tactics);
        return state.placedCount === N;
    }

    // Full-solve difficulty replay. Same order as solveWithTactics
    // (T2 → T4 → T3 → T5) but records each firing so the generator
    // can rank candidate puzzles by
    //   sumScore  — total scoreStep across every deduction step,
    //   peakScore — hardest single step, and
    //   stepCounts — tier histogram, useful for debugging odd puzzles.
    // T1 kills are implicit in placeAt so they don't get their own
    // scoring turn (scoreStep charges 0 for T1 anyway).
    function scoreSolve(regions, N, tactics) {
        const state = makeSolverState(regions, N);
        let sumScore = 0;
        let peakScore = 0;
        const stepCounts = { T2: 0, T3: 0, T4: 0, T5: 0 };
        let safety = N * N * 4;
        while (safety-- > 0) {
            // Snapshot the candidate pool BEFORE this step so scoreStep
            // can adjust by "how much of the board was still in play"
            // at the moment the deduction fired.
            let poolBefore = 0;
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (state.candidate[r][c]) poolBefore += 1;
                }
            }
            let result = null;
            if (tactics.T2) result = stepT2(state);
            if (!result && tactics.T4) result = stepT4(state);
            if (!result && tactics.T3) result = stepT3(state);
            if (!result && tactics.T5) result = stepT5(state);
            if (!result) break;
            const excludedThis = progressSizeOf(result);
            const { score } = scoreStep(result, regions,
                { poolBefore, excludedThis, N });
            sumScore += score;
            if (score > peakScore) peakScore = score;
            stepCounts[result.tier] = (stepCounts[result.tier] || 0) + 1;
        }
        return {
            sumScore: Math.round(sumScore * 100) / 100,
            peakScore: Math.round(peakScore * 100) / 100,
            stepCounts,
            solved: state.placedCount === N,
        };
    }

    // -----------------------------------------------------------------
    // Region expansion — DFS with MRV cell ordering, random region
    // choice, full backtrack. Verifies each tentative assignment
    // against the tactic-bounded solver and only recurses if the
    // partial puzzle is still uniquely solvable.
    // -----------------------------------------------------------------

    function getAdjacentRegions(regions, r, c, N) {
        const set = new Set();
        if (r > 0 && regions[r - 1][c] !== -1) set.add(regions[r - 1][c]);
        if (r < N - 1 && regions[r + 1][c] !== -1) set.add(regions[r + 1][c]);
        if (c > 0 && regions[r][c - 1] !== -1) set.add(regions[r][c - 1]);
        if (c < N - 1 && regions[r][c + 1] !== -1) set.add(regions[r][c + 1]);
        return Array.from(set);
    }

    function expandRegions(N, queens, tactics, rng, deadline, maxLayouts) {
        const regions = Array.from({ length: N }, () => new Array(N).fill(-1));
        for (let r = 0; r < N; r++) {
            regions[r][queens[r]] = r;
        }
        // Region ID matches its seed row, so `regionSize[i]` tracks the
        // current cell count of region i. Starts at 1 (the seed queen).
        // Kept in sync with `regions[][]` mutation so the branch-order
        // heuristic below can consult it in O(1).
        const regionSize = new Array(N).fill(1);
        let unassigned = N * N - N;
        let steps = 0;          // total `step()` invocations
        let verifyCalls = 0;    // total tactic-bounded solver runs
        let verifyRejects = 0;  // verify said "not unique under tier"
        let backtracks = 0;     // recursed past verify but the subtree dead-ended
        let isolatedDeadEnds = 0; // unassigned cells with no frontier path
        let timedOut = false;

        // All valid, uniquely-solvable layouts collected on this
        // placeQueens. Each entry is a deep-copied snapshot of
        // `regions` at the moment DFS reached unassigned=0 with the
        // tactic-bounded solver confirming uniqueness. We keep
        // pushing until either `maxLayouts` are found (early-exit via
        // returning `true` up the recursion) or the DFS naturally
        // exhausts every branch, whichever comes first.
        const layouts = [];
        const cap = Math.max(1, maxLayouts || 1);

        // step() now returns a boolean:
        //   true  = stop climbing (either we hit maxLayouts or the
        //           deadline; either way, unwind cleanly).
        //   false = keep exploring more branches at this level.
        // The old "return regions" idiom is replaced by pushing into
        // `layouts` inside the base case.
        function step() {
            steps += 1;
            if ((steps & 0xff) === 0 && Date.now() > deadline) {
                timedOut = true;
                return true;
            }
            if (unassigned === 0) {
                verifyCalls += 1;
                if (verifyUniqueUnderTactics(regions, N, tactics)) {
                    layouts.push(regions.map(row => row.slice()));
                    if (layouts.length >= cap) return true;
                }
                return false; // continue backtracking to find more
            }

            // Build frontier: unassigned cells with ≥1 assigned 4-neighbour.
            // Compute MRV (fewest viable adjacent regions) on the fly.
            // 1-option cells are forced moves — they're picked first and
            // contribute zero branching, which is the dominant reason
            // generation feels fast: most of the board fills in along a
            // forced corridor before we hit a real branch.
            let bestR = -1, bestC = -1, bestOptions = null;
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (regions[r][c] !== -1) continue;
                    const opts = getAdjacentRegions(regions, r, c, N);
                    if (opts.length === 0) continue;
                    if (bestOptions === null || opts.length < bestOptions.length) {
                        bestR = r; bestC = c; bestOptions = opts;
                        if (opts.length === 1) break; // can't beat 1 option
                    }
                }
                if (bestOptions && bestOptions.length === 1) break;
            }

            if (bestOptions === null) {
                // No frontier — there are unassigned cells but none touch
                // any assigned region. Can't preserve 4-connectivity.
                isolatedDeadEnds += 1;
                return false;
            }

            // Order branches by current region size ascending, ties
            // broken by the seeded shuffle. This "grow the smallest
            // region first" heuristic pushes region sizes toward
            // parity, which in turn makes it much less likely that
            // some region ends up stuck at size 1 (a trivial T2
            // "region is a singleton → queen forced here" hint that
            // makes puzzles feel too easy). Sort is stable in ES2019+
            // so the shuffled tie order is preserved. Correctness of
            // the DFS is unaffected — it's still a full backtrack, we
            // only try smaller-first on each level.
            const shuffled = bestOptions.slice();
            PC.rng.shuffle(shuffled, rng);
            shuffled.sort((a, b) => regionSize[a] - regionSize[b]);

            for (const reg of shuffled) {
                regions[bestR][bestC] = reg;
                regionSize[reg] += 1;
                unassigned -= 1;
                verifyCalls += 1;
                let stop = false;
                if (verifyUniqueUnderTactics(regions, N, tactics)) {
                    stop = step();
                    if (!stop) backtracks += 1;
                } else {
                    verifyRejects += 1;
                }
                regions[bestR][bestC] = -1;
                regionSize[reg] -= 1;
                unassigned += 1;
                if (stop) return true;
            }
            return false;
        }

        step();
        return {
            layouts,
            steps,
            verifyCalls,
            verifyRejects,
            backtracks,
            isolatedDeadEnds,
            timedOut,
            maxLayouts: cap,
        };
    }

    // Post-hoc region-size summary for a single layout snapshot.
    // Pulled out of expandRegions because the multi-layout mode
    // hands back several snapshots and each needs its own stats.
    function layoutRegionStats(layout, N) {
        const sizes = new Array(N).fill(0);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const k = layout[r][c];
                if (k !== -1) sizes[k] += 1;
            }
        }
        let singletonRegions = 0;
        let tinyRegions = 0;
        let minRegionSize = Infinity;
        let maxRegionSize = 0;
        for (const s of sizes) {
            if (s === 1) singletonRegions += 1;
            if (s <= 2) tinyRegions += 1;
            if (s < minRegionSize) minRegionSize = s;
            if (s > maxRegionSize) maxRegionSize = s;
        }
        return {
            regionSize: sizes,
            singletonRegions,
            tinyRegions,
            minRegionSize: minRegionSize === Infinity ? 0 : minRegionSize,
            maxRegionSize,
        };
    }

    // -----------------------------------------------------------------
    // Puzzle assembly
    // -----------------------------------------------------------------

    function buildPuzzle(N, difficulty, seed, queens, regions, stats) {
        return {
            id: `queens-${N}x${N}-${difficulty}-${seed.toString(36)}`,
            game: 'queens',
            size: N,
            difficulty,
            regions,
            solution: queens,
            stats: stats || null,
        };
    }

    // -----------------------------------------------------------------
    // Generator entrypoint
    //
    // Async because we yield to the event loop between seed retries so
    // the page can paint the progress overlay. Progress callback (if
    // provided) is awaited with the retry-attempt fraction; within a
    // single attempt the bar stays indeterminate.
    // -----------------------------------------------------------------

    async function generate(size, difficulty, seed, onProgress) {
        const N = size;
        const tactics = TACTICS_BY_DIFFICULTY[difficulty] || TACTICS_BY_DIFFICULTY.medium;
        const quality = qualityTargets(N, difficulty);
        const targetCandidates = candidateBudget(N, difficulty);
        const maxRetries = maxSeedRetries(N, difficulty);
        const innerDepth = innerSearchDepth(N, difficulty);
        const tStart = Date.now();
        // Timeout scaled by innerDepth — collecting K layouts per
        // seed does roughly K× the DFS work of the original one-shot,
        // and we don't want the deadline to cut us off before the
        // extra layouts get a chance.
        const timeout = attemptTimeoutMs(N) * Math.max(1, innerDepth);
        dbg('generate', {
            N, difficulty, seed: seed.toString(16),
            timeout, quality, targetCandidates, maxRetries, innerDepth,
        });

        let lastFailReason = 'no-attempt';
        // Collected candidate puzzles across seed retries. Each one
        // is an already-verified, uniquely-solvable puzzle scored
        // under the difficulty's tactic set. Sorted at the end by
        // compareCandidates — quality-first, then hardness — and
        // the winner is returned. Easy sets targetCandidates=1 so
        // it short-circuits on the first quality pass; medium/hard
        // sample multiple to steer for higher difficulty scores.
        const candidates = [];

        for (let retry = 0; retry < maxRetries; retry++) {
            if (onProgress) {
                await onProgress(retry / maxRetries);
            }
            const retrySeed = (seed ^ ((retry + 1) * 0x9e3779b9)) >>> 0;
            const rng = PC.rng.make(retrySeed);
            const tAttempt = Date.now();
            const queens = placeQueens(N, rng);
            if (!queens) { lastFailReason = 'placeQueens-failed'; continue; }

            const deadline = tAttempt + timeout;
            const expand = expandRegions(N, queens, tactics, rng, deadline,
                innerDepth);
            const dt = Date.now() - tAttempt;
            if (!expand.layouts.length) {
                lastFailReason = expand.timedOut ? 'timeout' : 'exhausted';
                dbg('attempt', retry + 1, {
                    queens: queens.join(','),
                    steps: expand.steps,
                    ms: dt,
                    ok: false,
                    timedOut: expand.timedOut,
                });
                continue;
            }

            dbg('attempt', retry + 1, {
                queens: queens.join(','),
                layouts: expand.layouts.length,
                ms: dt,
                ok: true,
                timedOut: expand.timedOut,
            });

            // Every layout out of this seed is scored independently
            // and added as its own candidate. This is what makes B
            // (inner search depth) work: one seed can now feed
            // several distinct region layouts into the picker.
            for (const layout of expand.layouts) {
                const regionStats = layoutRegionStats(layout, N);
                const score = scoreSolve(layout, N, tactics);
                const stats = {
                    seedRetries: retry + 1,
                    innerDepth,
                    layoutsThisSeed: expand.layouts.length,
                    expandSteps: expand.steps,
                    verifyCalls: expand.verifyCalls,
                    verifyRejects: expand.verifyRejects,
                    backtracks: expand.backtracks,
                    isolatedDeadEnds: expand.isolatedDeadEnds,
                    singletonRegions: regionStats.singletonRegions,
                    tinyRegions: regionStats.tinyRegions,
                    minRegionSize: regionStats.minRegionSize,
                    maxRegionSize: regionStats.maxRegionSize,
                    sumScore: score.sumScore,
                    peakScore: score.peakScore,
                    stepCounts: score.stepCounts,
                    genMs: Date.now() - tStart,
                    attemptMs: dt,
                    timeoutMs: timeout,
                };
                candidates.push({ queens, regions: layout, stats });
            }

            // We've collected enough quality-passing samples — stop
            // early. Sampling extra retries beyond this would just
            // spend wall time for a marginal chance at a harder seed.
            const qualityPassCount = candidates.reduce((n, c) =>
                n + (meetsQuality(c.stats, quality) ? 1 : 0), 0);
            if (qualityPassCount >= targetCandidates) break;
        }

        if (candidates.length === 0) {
            // Every retry failed to expand. Same behaviour as before:
            // fall back to throwing so the caller notices.
            throw new Error(
                `queens generator: ${maxRetries} retries exhausted ` +
                `(last reason: ${lastFailReason}, N=${N}, difficulty=${difficulty})`,
            );
        }

        candidates.sort((a, b) => compareCandidates(a, b, quality));
        const winner = candidates[0];
        winner.stats.candidateCount = candidates.length;
        winner.stats.candidateBudget = targetCandidates;
        winner.stats.maxRetries = maxRetries;
        // Debug breadcrumb — how many candidates we sampled and what
        // the score spread looked like, so trace-tool users can tell
        // whether the picker had any meaningful room to choose.
        winner.stats.candidateSpread = candidates.map(c => ({
            sumScore: c.stats.sumScore,
            peakScore: c.stats.peakScore,
            singletons: c.stats.singletonRegions,
            tinies: c.stats.tinyRegions,
        }));
        if (!meetsQuality(winner.stats, quality)) {
            winner.stats.qualityMissed = true;
            winner.stats.qualityTarget = {
                maxSingletonRegions: quality.maxSingletonRegions,
                maxTinyRegions: quality.maxTinyRegions,
            };
        }
        if (onProgress) await onProgress(1);
        return buildPuzzle(N, difficulty, seed, winner.queens,
            winner.regions, winner.stats);
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.queens = generate;

    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleSolvers.queens = {
        TACTICS_BY_DIFFICULTY,
        placeQueens,
        solveWithTactics,
        verifyUniqueUnderTactics,
        expandRegions,
        // Exposed for the trace tool AND the in-game hint system.
        makeSolverState,
        placeAt,
        excludeAt,
        stepT2,
        stepT3,
        stepT4,
        stepT5,
        scoreStep,
        scoreSolve,
    };
})(window);
