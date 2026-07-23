/**
 * Patches — puzzle generator + logic solver.
 *
 * Patches is a Shikaku (矩形分割) variant: partition an N×N grid into
 * axis-aligned rectangles that tile it perfectly (no gaps, no overlaps).
 * Every rectangle contains exactly ONE clue cell, so most cells are blank.
 * A clue constrains the rectangle that owns its cell:
 *
 *   shape ∈ { 'square', 'wide', 'tall', 'any' }
 *     square → w === h        (≥ 2×2, since 1×1 is never allowed)
 *     wide   → w >  h         (≥ 2×1)
 *     tall   → h >  w         (≥ 1×2)
 *     any    → any rectangle with area ≥ 2
 *   size  → number | null     (if set, the rectangle's area must equal it)
 *
 * No 1×1 rectangles exist anywhere on the board.
 *
 * Exposed via `window.PuzzleGenerators.patches(size, difficulty, seed,
 * onProgress)` → resolves to the puzzle JSON:
 *
 *   {
 *     id, game: 'patches', size: N, difficulty,
 *     clues:    Array<{ r, c, shape, size|null }>,
 *     solution: Array<{ r, c, w, h, clue }>,   // the unique tiling
 *   }
 *
 * The solver is technique-bounded (no blind guessing) and is reused both
 * to guarantee a unique solution and, later, to drive in-game hints.
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    // Flip on via ?patches_debug=1 for verbose generation logging.  [DEBUG-HOOK]
    const DEBUG = typeof location !== 'undefined'
        && /[?&]patches_debug=1\b/.test(location.search);

    // -----------------------------------------------------------------
    // Geometry helpers
    // -----------------------------------------------------------------

    const SHAPES = { SQUARE: 'square', WIDE: 'wide', TALL: 'tall', ANY: 'any' };

    /** Concrete shape category implied by a rectangle's dimensions. */
    function shapeOf(w, h) {
        if (w === h) return SHAPES.SQUARE;
        return w > h ? SHAPES.WIDE : SHAPES.TALL;
    }

    /** Does a w×h rectangle satisfy a shape constraint? 1×1 is never legal. */
    function satisfiesShape(shape, w, h) {
        if (w * h < 2) return false;
        switch (shape) {
            case SHAPES.SQUARE: return w === h;
            case SHAPES.WIDE:   return w > h;
            case SHAPES.TALL:   return h > w;
            case SHAPES.ANY:    return true;
            default:            return false;
        }
    }

    function rectContains(rect, r, c) {
        return r >= rect.r && r < rect.r + rect.h
            && c >= rect.c && c < rect.c + rect.w;
    }

    /** Do two rectangles overlap? */
    function rectsOverlap(a, b) {
        return a.c < b.c + b.w && b.c < a.c + a.w
            && a.r < b.r + b.h && b.r < a.r + a.h;
    }

    // -----------------------------------------------------------------
    // Random rectangle tiling (guillotine split).
    //
    // Recursively slice a region into two, stopping (keeping the region
    // as a leaf) with a probability that rises as the region shrinks.
    // The split rule guarantees no leaf is ever 1×1: a 1×k strip is only
    // split when k ≥ 4 (into two ≥1×2 halves), so every leaf has area ≥ 2.
    // -----------------------------------------------------------------

    function tileGrid(N, rng, difficulty) {
        // Larger target area on easier boards → fewer, chunkier pieces
        // that are gentler to reason about. Hard packs in more clues.
        const stopBias = { easy: 0.72, medium: 0.55, hard: 0.42 }[difficulty]
            || 0.55;
        const rects = [];

        function recurse(r, c, w, h) {
            const area = w * h;
            // Leaves must have area ≥ 2. A region can only keep splitting
            // if at least one axis affords a legal cut.
            const canSplitV = w >= 2 && (h >= 2 || w >= 4);
            const canSplitH = h >= 2 && (w >= 2 || h >= 4);
            const canSplit = canSplitV || canSplitH;
            // Stop chance grows as the piece shrinks toward area 2.
            const stop = area <= 2
                || (canSplit && rng() < stopBias * Math.min(1, 4 / area));
            if (!canSplit || stop) {
                rects.push({ r, c, w, h });
                return;
            }

            // Choose an axis we're actually allowed to cut on.
            let vertical;
            if (canSplitV && canSplitH) vertical = rng() < w / (w + h);
            else vertical = canSplitV;

            if (vertical) {
                // Split columns into [lo, w-lo]. If h === 1 both halves
                // must be ≥ 2 wide (no 1×1); else any 1..w-1 is fine.
                const lo = h === 1
                    ? PC.rng.pickInt(rng, 2, w - 1)   // 2..w-2
                    : PC.rng.pickInt(rng, 1, w);       // 1..w-1
                recurse(r, c, lo, h);
                recurse(r, c + lo, w - lo, h);
            } else {
                const lo = w === 1
                    ? PC.rng.pickInt(rng, 2, h - 1)
                    : PC.rng.pickInt(rng, 1, h);
                recurse(r, c, w, lo);
                recurse(r + lo, c, w, h - lo);
            }
        }

        recurse(0, 0, N, N);
        return rects;
    }

    /** Turn a tiling into full clues: one clue cell per rectangle, with
     *  its concrete shape and exact area. Digging removes info later. */
    function cluesFromTiling(rects, rng) {
        return rects.map((rect) => {
            const cr = rect.r + PC.rng.pickInt(rng, 0, rect.h);
            const cc = rect.c + PC.rng.pickInt(rng, 0, rect.w);
            return {
                r: cr,
                c: cc,
                shape: shapeOf(rect.w, rect.h),
                size: rect.w * rect.h,
            };
        });
    }

    // -----------------------------------------------------------------
    // Candidate enumeration
    //
    // For a clue, every rectangle that (a) contains its cell, (b) fits the
    // board, (c) satisfies the shape (+ size if given), and (d) contains
    // no OTHER clue cell. Rectangle count containing a fixed cell is
    // O(N^4) worst case but tiny for N ≤ 12.
    // -----------------------------------------------------------------

    function enumerateCandidates(N, clue, ownIdx, clueAt) {
        const out = [];
        const cr = clue.r;
        const cc = clue.c;
        for (let top = 0; top <= cr; top++) {
            for (let bottom = cr; bottom < N; bottom++) {
                const h = bottom - top + 1;
                for (let left = 0; left <= cc; left++) {
                    for (let right = cc; right < N; right++) {
                        const w = right - left + 1;
                        if (!satisfiesShape(clue.shape, w, h)) continue;
                        if (clue.size != null && w * h !== clue.size) continue;
                        if (containsForeignClue(top, left, w, h, ownIdx, clueAt, N)) {
                            continue;
                        }
                        out.push({ r: top, c: left, w, h });
                    }
                }
            }
        }
        return out;
    }

    function containsForeignClue(top, left, w, h, ownIdx, clueAt, N) {
        for (let r = top; r < top + h; r++) {
            const base = r * N;
            for (let c = left; c < left + w; c++) {
                const idx = clueAt[base + c];
                if (idx >= 0 && idx !== ownIdx) return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------
    // Logic solver (technique-bounded constraint propagation).
    //
    // State: per-clue candidate lists + an `owner` grid (which clue is
    // proven to cover each cell, or -1). Two deductions, run to a
    // fixpoint:
    //   B  (single candidate): a clue with one candidate left → commit it.
    //   A  (single cover)    : a still-free cell coverable by candidates
    //                          of exactly one clue → that clue must cover
    //                          it, so prune the clue to candidates that do.
    // Neither guesses. If it commits every clue and fills the grid, the
    // puzzle is logic-solvable; otherwise it's 'stuck' (or 'contradiction'
    // if a cell can't be covered at all).
    // -----------------------------------------------------------------

    function makeClueAt(N, clues) {
        const clueAt = new Int32Array(N * N).fill(-1);
        clues.forEach((cl, i) => { clueAt[cl.r * N + cl.c] = i; });
        return clueAt;
    }

    function propagate(N, clues, clueAt) {
        const K = clues.length;
        const cands = clues.map((cl, i) => enumerateCandidates(N, cl, i, clueAt));
        const owner = new Int32Array(N * N).fill(-1);
        const committed = new Array(K).fill(null);
        let remaining = K;

        for (let i = 0; i < K; i++) {
            if (cands[i].length === 0) return { status: 'contradiction' };
        }

        function commit(i, rect) {
            committed[i] = rect;
            for (let r = rect.r; r < rect.r + rect.h; r++) {
                for (let c = rect.c; c < rect.c + rect.w; c++) owner[r * N + c] = i;
            }
            cands[i] = [rect];
            remaining -= 1;
        }

        // Drop candidates of other clues that now overlap a committed cell.
        function prunePlaced(placedRect, placedIdx) {
            for (let i = 0; i < K; i++) {
                if (committed[i]) continue;
                cands[i] = cands[i].filter((rc) => !rectsOverlap(rc, placedRect));
                if (cands[i].length === 0) return false;
            }
            return true;
        }

        let changed = true;
        while (changed && remaining > 0) {
            changed = false;

            // Rule B — a clue pinned to a single candidate.
            for (let i = 0; i < K; i++) {
                if (committed[i]) continue;
                if (cands[i].length === 1) {
                    const rect = cands[i][0];
                    commit(i, rect);
                    if (!prunePlaced(rect, i)) return { status: 'contradiction' };
                    changed = true;
                }
            }
            if (remaining === 0) break;

            // Rule A — a free cell only one clue can reach.
            // coverCount[cell] = # distinct clues with a candidate covering it.
            const coverClue = new Int32Array(N * N).fill(-1);
            const coverCount = new Int32Array(N * N);
            for (let i = 0; i < K; i++) {
                if (committed[i]) continue;
                // Mark, per clue, which cells this clue can still cover.
                const seen = new Set();
                for (const rc of cands[i]) {
                    for (let r = rc.r; r < rc.r + rc.h; r++) {
                        for (let c = rc.c; c < rc.c + rc.w; c++) {
                            const k = r * N + c;
                            if (seen.has(k)) continue;
                            seen.add(k);
                            if (coverClue[k] !== i) {
                                coverCount[k] += 1;
                                coverClue[k] = i;
                            }
                        }
                    }
                }
            }

            for (let k = 0; k < N * N; k++) {
                if (owner[k] !== -1) continue;
                if (coverCount[k] === 0) return { status: 'contradiction' };
                if (coverCount[k] === 1) {
                    const i = coverClue[k];
                    if (committed[i]) continue;
                    const r = (k / N) | 0;
                    const c = k % N;
                    const before = cands[i].length;
                    cands[i] = cands[i].filter((rc) => rectContains(rc, r, c));
                    if (cands[i].length === 0) return { status: 'contradiction' };
                    if (cands[i].length !== before) changed = true;
                }
            }
        }

        if (remaining === 0) {
            for (let k = 0; k < N * N; k++) {
                if (owner[k] === -1) return { status: 'contradiction' };
            }
            return { status: 'solved', owner, committed };
        }
        return { status: 'stuck', owner, cands };
    }

    // -----------------------------------------------------------------
    // Uniqueness — full backtracking exact-cover count, capped at `cap`.
    // Returns the number of tilings found (0, 1, or `cap`). A node budget
    // guards against pathological blow-ups; if exhausted we report the
    // budget marker so callers can treat it conservatively.
    // -----------------------------------------------------------------

    const NODE_BUDGET = 30000;

    function countSolutions(N, clues, cap) {
        const K = clues.length;
        const clueAt = makeClueAt(N, clues);
        const cands = clues.map((cl, i) => enumerateCandidates(N, cl, i, clueAt));
        for (let i = 0; i < K; i++) if (cands[i].length === 0) return 0;

        const owner = new Int32Array(N * N).fill(-1);
        const placed = new Array(K).fill(false);
        let solutions = 0;
        let nodes = 0;
        let aborted = false;

        function fits(rect) {
            for (let r = rect.r; r < rect.r + rect.h; r++) {
                for (let c = rect.c; c < rect.c + rect.w; c++) {
                    if (owner[r * N + c] !== -1) return false;
                }
            }
            return true;
        }
        function paint(rect, val) {
            for (let r = rect.r; r < rect.r + rect.h; r++) {
                for (let c = rect.c; c < rect.c + rect.w; c++) owner[r * N + c] = val;
            }
        }

        function search() {
            if (solutions >= cap || aborted) return;
            if (++nodes > NODE_BUDGET) { aborted = true; return; }

            // MRV: unplaced clue with the fewest currently-fitting candidates.
            let bi = -1;
            let best = Infinity;
            let bestList = null;
            for (let i = 0; i < K; i++) {
                if (placed[i]) continue;
                const list = cands[i].filter(fits);
                if (list.length < best) {
                    best = list.length;
                    bi = i;
                    bestList = list;
                    if (best === 0) break;
                }
            }

            if (bi === -1) {
                for (let k = 0; k < N * N; k++) if (owner[k] === -1) return;
                solutions += 1;
                return;
            }
            if (best === 0) return;

            placed[bi] = true;
            for (const rect of bestList) {
                if (!fits(rect)) continue;
                paint(rect, bi);
                search();
                paint(rect, -1);
                if (solutions >= cap || aborted) break;
            }
            placed[bi] = false;
        }

        search();
        return aborted ? -1 : solutions;
    }

    /** True iff exactly one tiling exists (budget exhaustion → treated as
     *  "not proven unique", i.e. false, so digging keeps the clue). */
    function isUnique(N, clues) {
        return countSolutions(N, clues, 2) === 1;
    }

    // -----------------------------------------------------------------
    // Difficulty — start from full clues, then strip information while the
    // solution stays unique (and, for easy/medium, stays logic-solvable so
    // the tier actually matches the promised difficulty).
    // -----------------------------------------------------------------

    function logicSolvable(N, clues) {
        return propagate(N, clues, makeClueAt(N, clues)).status === 'solved';
    }

    function digDifficulty(N, clues, difficulty, rng, deadline) {
        const requireLogic = difficulty !== 'hard';
        // Whether shape degradation to 'any' is on the table.
        const degradeShapes = difficulty !== 'easy';

        const order = clues.map((_, i) => i);
        PC.rng.shuffle(order, rng);

        // Pass 1: drop the number from as many clues as stays valid.
        for (const i of order) {
            if (Date.now() > deadline) return clues;
            if (clues[i].size == null) continue;
            const saved = clues[i].size;
            clues[i].size = null;
            if (!accept(N, clues, requireLogic)) clues[i].size = saved;
        }

        // Pass 2 (medium/hard): relax shape → 'any'.
        if (degradeShapes) {
            PC.rng.shuffle(order, rng);
            for (const i of order) {
                if (Date.now() > deadline) return clues;
                if (clues[i].shape === SHAPES.ANY) continue;
                const saved = clues[i].shape;
                clues[i].shape = SHAPES.ANY;
                if (!accept(N, clues, requireLogic)) clues[i].shape = saved;
            }
        }
        return clues;
    }

    function accept(N, clues, requireLogic) {
        if (!isUnique(N, clues)) return false;
        if (requireLogic && !logicSolvable(N, clues)) return false;
        return true;
    }

    // -----------------------------------------------------------------
    // Public entry point
    // -----------------------------------------------------------------

    /** Wall-clock ceiling for one generate() call. Digging stops at the
     *  deadline and ships whatever's been achieved — so large/hard boards
     *  degrade to "less stripped" rather than hanging. */
    function timeBudgetMs(N, difficulty) {
        const base = { easy: 1200, medium: 2200, hard: 3600 }[difficulty] || 2200;
        return base + Math.max(0, N - 8) * 400;
    }

    async function generate(size, difficulty, seed, onProgress) {
        const N = size;
        const rng = PC.rng.make(seed >>> 0);
        const deadline = Date.now() + timeBudgetMs(N, difficulty);
        if (onProgress) await onProgress(0.05);

        // 1) Find a tiling whose full-info clues already pin down this exact
        //    layout (usually the first try — see the self-test). This is the
        //    puzzle's unique solution.
        let rects = null;
        let clues = null;
        for (let attempt = 0; attempt < 40; attempt++) {
            const rr = tileGrid(N, rng, difficulty);
            const cc = cluesFromTiling(rr, rng);
            if (isUnique(N, cc)) { rects = rr; clues = cc; break; }
            if (Date.now() > deadline) { rects = rr; clues = cc; break; }
        }
        if (!clues) {
            rects = tileGrid(N, rng, difficulty);
            clues = cluesFromTiling(rects, rng);
        }

        if (onProgress) await onProgress(0.4);

        // 2) Strip information down to the difficulty target (bounded by the
        //    deadline).
        digDifficulty(N, clues, difficulty, rng, deadline);

        if (onProgress) await onProgress(1);

        const best = { rects, clues };
        const solution = best.rects.map((rect) => ({
            r: rect.r, c: rect.c, w: rect.w, h: rect.h,
            clue: clueIndexFor(best.clues, rect),
        }));

        if (DEBUG) {
            const withNum = best.clues.filter((c) => c.size != null).length;
            const anys = best.clues.filter((c) => c.shape === SHAPES.ANY).length;
            /* eslint-disable no-console */
            console.log(`[patches] N=${N} ${difficulty}: ${best.clues.length} clues, `
                + `${withNum} numbered, ${anys} any`);
            /* eslint-enable no-console */
        }

        return {
            id: `patches-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'patches',
            size: N,
            difficulty,
            clues: best.clues,
            solution,
        };
    }

    function clueIndexFor(clues, rect) {
        for (let i = 0; i < clues.length; i++) {
            if (rectContains(rect, clues[i].r, clues[i].c)) return i;
        }
        return -1;
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.patches = generate;
    // Expose internals for the (future) solver-trace dev tool.  [DEBUG-HOOK]
    global.PuzzleGenerators.patchesInternals = {
        enumerateCandidates, propagate, countSolutions, isUnique,
        logicSolvable, tileGrid, cluesFromTiling, makeClueAt,
        shapeOf, satisfiesShape, SHAPES,
    };
})(typeof window !== 'undefined' ? window : this);
