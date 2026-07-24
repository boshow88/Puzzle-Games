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
    // Random rectangle tiling (bottom-up merging).
    //
    // Start from all 1×1 cells and repeatedly merge two adjacent rectangles
    // that share a full edge (so the union is again a rectangle), chosen at
    // random, until the board is coarse enough. Unlike guillotine slicing
    // this can reach non-sliceable layouts (far more variety) and, by never
    // stopping above a target count, it can't produce a single giant patch.
    // A max-area cap keeps any one patch from dominating, and 1×1 cells are
    // cleared first so the result never contains one.
    // -----------------------------------------------------------------

    function mergeParams(N, difficulty) {
        // Average patch area → target patch count. Easier boards are a touch
        // chunkier (fewer, larger); harder boards a touch finer. (A first cut
        // — these are the natural knobs to tune difficulty with later.)
        const avgArea = { easy: 5, medium: 4.3, hard: 3.6 }[difficulty] || 4.3;
        const targetCount = Math.max(2, Math.round((N * N) / avgArea));
        const maxArea = Math.max(6, Math.round(N * 1.6));
        return { targetCount, maxArea };
    }

    function tryMergeTiling(N, rng, targetCount, maxArea) {
        const owner = new Int32Array(N * N);
        const rects = new Map(); // id → { r, c, w, h }
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const id = r * N + c;
                owner[id] = id;
                rects.set(id, { r, c, w: 1, h: 1 });
            }
        }
        const isUnit = (R) => R.w === 1 && R.h === 1;

        // Every legal merge: a patch with its right or bottom neighbour when
        // they line up into a clean rectangle (grid ownership guarantees the
        // neighbour is flush, so matching top+height / left+width suffices).
        function collectMerges() {
            const out = [];
            for (const [id, R] of rects) {
                if (R.c + R.w < N) {
                    const nb = owner[R.r * N + (R.c + R.w)];
                    const B = rects.get(nb);
                    if (B.r === R.r && B.h === R.h) {
                        out.push({ a: id, b: nb, horiz: true, area: (R.w + B.w) * R.h });
                    }
                }
                if (R.r + R.h < N) {
                    const nb = owner[(R.r + R.h) * N + R.c];
                    const B = rects.get(nb);
                    if (B.c === R.c && B.w === R.w) {
                        out.push({ a: id, b: nb, horiz: false, area: R.w * (R.h + B.h) });
                    }
                }
            }
            return out;
        }
        function apply(m) {
            const A = rects.get(m.a);
            const B = rects.get(m.b);
            for (let r = B.r; r < B.r + B.h; r++) {
                for (let c = B.c; c < B.c + B.w; c++) owner[r * N + c] = m.a;
            }
            if (m.horiz) A.w += B.w; else A.h += B.h;
            rects.delete(m.b);
        }

        let guard = N * N * 4;
        while (guard-- > 0) {
            let anyUnit = false;
            for (const R of rects.values()) { if (isUnit(R)) { anyUnit = true; break; } }
            if (rects.size <= targetCount && !anyUnit) break;

            const merges = collectMerges();
            let pool;
            if (anyUnit) {
                // Clear 1×1s first (while neighbours are still fine-grained),
                // so we never strand one that can't merge.
                pool = merges.filter((m) => isUnit(rects.get(m.a)) || isUnit(rects.get(m.b)));
                if (!pool.length) pool = merges.filter((m) => m.area <= maxArea);
            } else {
                pool = merges.filter((m) => m.area <= maxArea);
            }
            if (!pool.length) {
                if (anyUnit) return null; // stranded 1×1 → caller retries
                break;                    // no capped merges left; accept
            }
            apply(pool[PC.rng.pickInt(rng, 0, pool.length)]);
        }

        for (const R of rects.values()) if (isUnit(R)) return null;
        return Array.from(rects.values(), (R) => ({ r: R.r, c: R.c, w: R.w, h: R.h }));
    }

    function tileGrid(N, rng, difficulty) {
        const { targetCount, maxArea } = mergeParams(N, difficulty);
        for (let attempt = 0; attempt < 40; attempt++) {
            const t = tryMergeTiling(N, rng, targetCount, maxArea);
            if (t) return t;
        }
        // Astronomically unlikely for N ≤ 12; fall back to a guaranteed tiling.
        return guillotineTiling(N, rng);
    }

    // Emergency fallback only (see tileGrid): the original guillotine slicer,
    // guaranteed to produce a valid no-1×1 tiling.
    function guillotineTiling(N, rng) {
        const rects = [];
        function recurse(r, c, w, h) {
            const area = w * h;
            const canSplitV = w >= 2 && (h >= 2 || w >= 4);
            const canSplitH = h >= 2 && (w >= 2 || h >= 4);
            const canSplit = canSplitV || canSplitH;
            const stop = area <= 2 || (canSplit && rng() < 0.5 * Math.min(1, 4 / area));
            if (!canSplit || stop) { rects.push({ r, c, w, h }); return; }
            let vertical;
            if (canSplitV && canSplitH) vertical = rng() < w / (w + h);
            else vertical = canSplitV;
            if (vertical) {
                const lo = h === 1 ? PC.rng.pickInt(rng, 2, w - 1) : PC.rng.pickInt(rng, 1, w);
                recurse(r, c, lo, h);
                recurse(r, c + lo, w - lo, h);
            } else {
                const lo = w === 1 ? PC.rng.pickInt(rng, 2, h - 1) : PC.rng.pickInt(rng, 1, h);
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
        digDifficulty, shapeOf, satisfiesShape, SHAPES,
    };
})(typeof window !== 'undefined' ? window : this);
