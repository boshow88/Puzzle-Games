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
    // Logic solver (technique-bounded, single-step model — mirrors the
    // structure of sudoku.js so the SAME techniques drive both the
    // generator's difficulty grading and the in-game hints).
    //
    // State (see makeState): per-clue candidate rectangle lists + an
    // `owner` grid (which clue is proven to cover each cell, or -1).
    // `nextStep` returns the single easiest applicable deduction (or null);
    // `solveWithTechniques` applies steps to a fixpoint. Difficulty just
    // selects which techniques are switched on.
    //
    // Techniques, weakest first (each tier a strict superset):
    //   single : Rule B (a clue with one candidate left → commit it) and
    //            Rule A (a free cell only one clue can reach → that clue
    //            must cover it, so prune to candidates that do).
    //   core   : if EVERY candidate of a clue covers cell X, then X is that
    //            clue's no matter how it is finally drawn — lock X and forbid
    //            other clues there. (Rule B is the extreme single-candidate
    //            case of this.)
    //   orphan : 1-ply reachability. If placing a candidate would leave some
    //            free cell with no possible cover at all, that candidate
    //            can't be in any tiling — drop it. ("put it there and that
    //            corner can never be filled.")
    // Every technique is sound (it only removes rectangles that cannot be in
    // ANY tiling), so a bounded solve that reaches a full cover proves that
    // cover is the unique solution — the digger relies on exactly this.
    // -----------------------------------------------------------------

    const TECHNIQUES_BY_DIFFICULTY = {
        easy: { single: true },
        medium: { single: true, core: true },
        hard: { single: true, core: true, orphan: true },
    };

    function makeClueAt(N, clues) {
        const clueAt = new Int32Array(N * N).fill(-1);
        clues.forEach((cl, i) => { clueAt[cl.r * N + cl.c] = i; });
        return clueAt;
    }

    /** Does `outer` fully cover the smaller rect `inner`? */
    function coversRect(outer, inner) {
        return outer.r <= inner.r && outer.c <= inner.c
            && outer.r + outer.h >= inner.r + inner.h
            && outer.c + outer.w >= inner.c + inner.w;
    }

    /** True iff `rect` covers no cell already owned by a DIFFERENT clue. */
    function fitsOwner(st, rect, i) {
        for (let r = rect.r; r < rect.r + rect.h; r++) {
            for (let c = rect.c; c < rect.c + rect.w; c++) {
                const o = st.owner[r * st.N + c];
                if (o !== -1 && o !== i) return false;
            }
        }
        return true;
    }

    /** Build a fresh solver state. `seed` (optional) is a list of player
     *  placements {r,c,w,h,clue} treated as LOWER BOUNDS: each clue's
     *  candidates are restricted to rectangles that cover its placement and
     *  the placement's cells are marked owned, but the clue may still grow.
     *  The in-game hint engine passes the player's current rectangles here. */
    function makeState(N, clues, seed) {
        const K = clues.length;
        const clueAt = makeClueAt(N, clues);
        const cands = clues.map((cl, i) => enumerateCandidates(N, cl, i, clueAt));
        const owner = new Int32Array(N * N).fill(-1);
        const st = {
            N, K, clues, clueAt, cands, owner,
            committed: new Array(K).fill(null), remaining: K, dead: false,
        };
        if (seed) {
            for (const pl of seed) {
                const i = pl.clue;
                cands[i] = cands[i].filter((rc) => coversRect(rc, pl));
                for (let r = pl.r; r < pl.r + pl.h; r++) {
                    for (let c = pl.c; c < pl.c + pl.w; c++) owner[r * N + c] = i;
                }
            }
            for (let i = 0; i < K; i++) {
                cands[i] = cands[i].filter((rc) => fitsOwner(st, rc, i));
            }
            // A seeded clue that can no longer grow (its only candidate is
            // exactly what's already drawn) is DONE — commit it so nextStep
            // won't keep re-suggesting an already-placed rectangle.
            for (const pl of seed) {
                const i = pl.clue;
                const only = cands[i][0];
                if (cands[i].length === 1 && only.r === pl.r && only.c === pl.c
                    && only.w === pl.w && only.h === pl.h && !st.committed[i]) {
                    st.committed[i] = only;
                    st.remaining -= 1;
                }
            }
        }
        for (let i = 0; i < K; i++) if (cands[i].length === 0) st.dead = true;
        return st;
    }

    /** coverClue[cell] / coverCount[cell] over the UNCOMMITTED clues. */
    function coverage(st) {
        const N = st.N;
        const clue = new Int32Array(N * N).fill(-1);
        const count = new Int32Array(N * N);
        for (let i = 0; i < st.K; i++) {
            if (st.committed[i]) continue;
            const seen = new Set();
            for (const rc of st.cands[i]) {
                for (let r = rc.r; r < rc.r + rc.h; r++) {
                    for (let c = rc.c; c < rc.c + rc.w; c++) {
                        const k = r * N + c;
                        if (seen.has(k)) continue;
                        seen.add(k);
                        if (clue[k] !== i) { count[k] += 1; clue[k] = i; }
                    }
                }
            }
        }
        return { clue, count };
    }

    function otherCanCover(st, r, c, i) {
        for (let j = 0; j < st.K; j++) {
            if (j === i || st.committed[j]) continue;
            for (const rc of st.cands[j]) if (rectContains(rc, r, c)) return true;
        }
        return false;
    }

    // --- techniques: each COLLECTS every deduction of its kind, so the hint
    //     layer can drop suggestions dominated by a bigger one before picking
    //     (mirrors tango's findLowestAvailableTier). ----------------------

    function singleDeductions(st) {
        const commits = [];
        for (let i = 0; i < st.K; i++) {
            if (st.committed[i]) continue;
            if (st.cands[i].length === 1) {
                commits.push({ technique: 'single', kind: 'commit', clue: i, rect: st.cands[i][0] });
            }
        }
        const forceCells = [];
        const cov = coverage(st);
        for (let k = 0; k < st.N * st.N; k++) {
            if (st.owner[k] !== -1) continue;
            if (cov.count[k] === 0) { st.dead = true; return { commits, forceCells }; }
            if (cov.count[k] !== 1) continue;
            const i = cov.clue[k];
            if (st.committed[i]) continue;
            const r = (k / st.N) | 0, c = k % st.N;
            if (st.cands[i].some((rc) => !rectContains(rc, r, c))) {
                forceCells.push({ technique: 'single', kind: 'forceCell', clue: i, cell: [r, c] });
            }
        }
        return { commits, forceCells };
    }

    function coreDeductions(st) {
        const N = st.N;
        const out = [];
        for (let i = 0; i < st.K; i++) {
            if (st.committed[i]) continue;
            const list = st.cands[i];
            if (list.length < 2) continue; // length 1 → Rule B; 0 → dead
            const cnt = new Map();
            for (const rc of list) {
                for (let r = rc.r; r < rc.r + rc.h; r++) {
                    for (let c = rc.c; c < rc.c + rc.w; c++) {
                        const k = r * N + c;
                        cnt.set(k, (cnt.get(k) || 0) + 1);
                    }
                }
            }
            for (const [k, n] of cnt) {
                if (n !== list.length) continue;   // not covered by EVERY candidate
                if (st.owner[k] === i) continue;    // already locked to i
                const r = (k / N) | 0, c = k % N;
                // Only interesting when another clue could also reach k (else
                // Rule A already handles it); applying prunes those clues.
                if (otherCanCover(st, r, c, i)) {
                    out.push({ technique: 'core', kind: 'forceCell', clue: i, cell: [r, c] });
                }
            }
        }
        return out;
    }

    // 1-ply reachability, restricted to "fragile" free cells (reachable by only
    // a few clues) so the scan stays cheap. Collect every candidate whose
    // placement would strand such a cell — those can't be in any tiling.
    const ORPHAN_MAX_COVER = 3;
    // Returns Map(candidateRect → { strand:[r,c], clue }) — each dead candidate
    // paired with the fragile cell its placement would strand (and whose clue
    // it belongs to), so the hint can point at the victim.
    function collectDeadCandidates(st) {
        const N = st.N;
        const cov = coverage(st);
        const dead = new Map();
        for (let k = 0; k < N * N; k++) {
            if (st.owner[k] !== -1) continue;
            const cnt = cov.count[k];
            if (cnt < 2 || cnt > ORPHAN_MAX_COVER) continue;
            const kr = (k / N) | 0, kc = k % N;
            const groups = [];
            for (let i = 0; i < st.K; i++) {
                if (st.committed[i]) continue;
                let reach = null;
                for (const rc of st.cands[i]) {
                    if (rectContains(rc, kr, kc)) (reach || (reach = [])).push(rc);
                }
                if (reach) groups.push({ i, reach });
            }
            if (groups.length !== cnt) continue; // defensive
            for (let i = 0; i < st.K; i++) {
                if (st.committed[i]) continue;
                for (const rc of st.cands[i]) {
                    if (dead.has(rc) || rectContains(rc, kr, kc)) continue;
                    let kills = true;
                    for (const g of groups) {
                        if (g.i === i) continue; // i becomes rc → its reach is gone
                        if (g.reach.some((br) => !rectsOverlap(br, rc))) { kills = false; break; }
                    }
                    if (kills) dead.set(rc, { strand: [kr, kc], clue: i });
                }
            }
        }
        return dead;
    }

    // Orphan expressed as POSITIVE deductions. A bare "this candidate is
    // impossible" elimination is useless to a Patches player — unlike sudoku
    // there are no candidate-notes to cross off. So instead: drop every dead
    // candidate, and whatever single/core placement that NEWLY enables is the
    // orphan result ("this cell must be X — any other clue reaching it would
    // strand a cell"). That's an actionable placement, not an elimination.
    function orphanDeductions(st) {
        const dead = collectDeadCandidates(st);
        if (dead.size === 0) return [];
        const shadow = {
            N: st.N, K: st.K, clues: st.clues, clueAt: st.clueAt,
            owner: st.owner, committed: st.committed, remaining: st.remaining, dead: false,
            cands: st.cands.map((list) => list.filter((rc) => !dead.has(rc))),
        };
        const single = singleDeductions(shadow);
        const core = coreDeductions(shadow);
        const out = single.commits.map((s) => Object.assign({}, s, { technique: 'orphan' }));
        for (const s of single.forceCells.concat(core)) {
            const o = Object.assign({}, s, { technique: 'orphan' });
            // The cell is forced because every OTHER clue that could reach it
            // has only dead candidates there. Surface one such victim — the
            // cell that would be stranded — plus the clue that would strand it.
            const [r, c] = s.cell;
            for (const [rc, info] of dead) {
                if (info.clue !== s.clue && rectContains(rc, r, c)) {
                    o.victim = info.strand;
                    o.viaClue = info.clue;
                    break;
                }
            }
            out.push(o);
        }
        return out;
    }

    // Every deduction at the LOWEST firing tier (single → core → orphan),
    // gated by `tech`. { tier, steps } or null.
    function findAllDeductions(st, tech) {
        const t = tech || TECHNIQUES_BY_DIFFICULTY.hard;
        if (st.dead) return null;
        if (t.single) {
            const { commits, forceCells } = singleDeductions(st);
            if (st.dead) return null;
            if (commits.length) return { tier: 'single', steps: commits };
            if (forceCells.length) return { tier: 'single', steps: forceCells };
        }
        if (t.core) {
            const fc = coreDeductions(st);
            if (fc.length) return { tier: 'core', steps: fc };
        }
        if (t.orphan) {
            const fc = orphanDeductions(st);
            if (fc.length) return { tier: 'orphan', steps: fc };
        }
        return null;
    }

    function nextStep(st, tech) {
        const r = findAllDeductions(st, tech);
        return r ? r.steps[0] : null;
    }

    function commitClue(st, i, rect) {
        const N = st.N;
        st.committed[i] = rect;
        for (let r = rect.r; r < rect.r + rect.h; r++) {
            for (let c = rect.c; c < rect.c + rect.w; c++) st.owner[r * N + c] = i;
        }
        st.cands[i] = [rect];
        st.remaining -= 1;
        for (let j = 0; j < st.K; j++) {
            if (j === i || st.committed[j]) continue;
            st.cands[j] = st.cands[j].filter((rc) => !rectsOverlap(rc, rect));
            if (st.cands[j].length === 0) st.dead = true;
        }
    }

    /** Apply a step in place; returns whether it changed anything. */
    function applyStep(st, step) {
        const N = st.N;
        if (step.kind === 'commit') { commitClue(st, step.clue, step.rect); return true; }
        if (step.kind === 'forceCell') {
            const i = step.clue, r = step.cell[0], c = step.cell[1];
            if (step.technique === 'core' || step.technique === 'orphan') {
                // Cell (r,c) is proven to belong to clue i — settle it: lock the
                // owner, keep only i's candidates covering it (no-op for core),
                // and forbid every other clue there.
                st.owner[r * N + c] = i;
                st.cands[i] = st.cands[i].filter((rc) => rectContains(rc, r, c));
                if (st.cands[i].length === 0) st.dead = true;
                for (let j = 0; j < st.K; j++) {
                    if (j === i || st.committed[j]) continue;
                    st.cands[j] = st.cands[j].filter((rc) => !rectContains(rc, r, c));
                    if (st.cands[j].length === 0) st.dead = true;
                }
                return true;
            }
            const before = st.cands[i].length;
            st.cands[i] = st.cands[i].filter((rc) => rectContains(rc, r, c));
            if (st.cands[i].length === 0) st.dead = true;
            return st.cands[i].length !== before;
        }
        return false;
    }

    /** Solve as far as the allowed techniques reach.
     *  Returns { solved, owner, remaining, counts, state }. */
    function solveWithTechniques(N, clues, tech, seed) {
        const st = makeState(N, clues, seed);
        const counts = {};
        // Elimination steps don't fill a clue, so bound by candidate count.
        let budget = N * N + 50;
        for (let i = 0; i < st.K; i++) budget += st.cands[i].length;
        for (let step = 0; step < budget; step++) {
            if (st.dead) break;
            const s = nextStep(st, tech);
            if (!s) break;
            counts[s.technique] = (counts[s.technique] || 0) + 1;
            if (!applyStep(st, s)) break;
        }
        let solved = !st.dead && st.remaining === 0;
        if (solved) {
            for (let k = 0; k < N * N; k++) if (st.owner[k] === -1) { solved = false; break; }
        }
        return { solved, owner: st.owner, remaining: st.remaining, counts, state: st };
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
    // puzzle stays solvable by EXACTLY the tier's technique set AND still
    // resolves to the SAME tiling. Solving back to the known solution is
    // both the uniqueness guarantee (sound techniques + full cover ⇒ unique)
    // and a soundness guard against a buggy technique (mirrors sudoku.js's
    // "solve must match the solution" acceptance test).
    // -----------------------------------------------------------------

    function logicSolvable(N, clues, tech) {
        return solveWithTechniques(N, clues, tech).solved;
    }

    function digDifficulty(N, clues, solutionOwner, difficulty, rng, deadline) {
        const tech = TECHNIQUES_BY_DIFFICULTY[difficulty]
            || TECHNIQUES_BY_DIFFICULTY.medium;
        // Whether shape degradation to 'any' is on the table.
        const degradeShapes = difficulty !== 'easy';

        const solvesToSolution = () => {
            const res = solveWithTechniques(N, clues, tech);
            if (!res.solved) return false;
            for (let k = 0; k < N * N; k++) {
                if (res.owner[k] !== solutionOwner[k]) return false;
            }
            return true;
        };

        const order = clues.map((_, i) => i);
        PC.rng.shuffle(order, rng);

        // Pass 1: drop the number from as many clues as the tier allows.
        for (const i of order) {
            if (Date.now() > deadline) return clues;
            if (clues[i].size == null) continue;
            const saved = clues[i].size;
            clues[i].size = null;
            if (!solvesToSolution()) clues[i].size = saved;
        }

        // Pass 2 (medium/hard): relax shape → 'any'.
        if (degradeShapes) {
            PC.rng.shuffle(order, rng);
            for (const i of order) {
                if (Date.now() > deadline) return clues;
                if (clues[i].shape === SHAPES.ANY) continue;
                const saved = clues[i].shape;
                clues[i].shape = SHAPES.ANY;
                if (!solvesToSolution()) clues[i].shape = saved;
            }
        }
        return clues;
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

        // Cell → clue index for the (known) solution tiling. cluesFromTiling
        // maps rects → clues in order, so rect i is clue i. The digger keeps
        // only strips that still resolve back to exactly this owner grid.
        const solutionOwner = new Int32Array(N * N).fill(-1);
        rects.forEach((rect, i) => {
            for (let r = rect.r; r < rect.r + rect.h; r++) {
                for (let c = rect.c; c < rect.c + rect.w; c++) solutionOwner[r * N + c] = i;
            }
        });

        // 2) Strip information down to the difficulty target (bounded by the
        //    deadline).
        digDifficulty(N, clues, solutionOwner, difficulty, rng, deadline);

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
        enumerateCandidates, countSolutions, isUnique,
        makeState, nextStep, applyStep, findAllDeductions, solveWithTechniques, coverage,
        TECHNIQUES_BY_DIFFICULTY, logicSolvable,
        tileGrid, cluesFromTiling, makeClueAt,
        digDifficulty, shapeOf, satisfiesShape, SHAPES,
    };

    // Solver surface, aligned with PuzzleSolvers.sudoku / .tango so games and
    // dev tools reach every game's solver the same way. `nextDeduction` is the
    // single-step convenience (mirrors tango): seed the state with the player's
    // placements and return the next step at the given technique set, or null.
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleSolvers.patches = {
        TECHNIQUES_BY_DIFFICULTY,
        makeState, nextStep, applyStep, findAllDeductions, solveWithTechniques,
        coverage, enumerateCandidates, makeClueAt, SHAPES,
        nextDeduction(N, clues, placements, tech) {
            return nextStep(makeState(N, clues, placements || []),
                tech || TECHNIQUES_BY_DIFFICULTY.hard);
        },
        // All deductions at the lowest firing tier for the given player
        // placements — the hint layer drops dominated suggestions then picks.
        allDeductions(N, clues, placements, tech) {
            return findAllDeductions(makeState(N, clues, placements || []),
                tech || TECHNIQUES_BY_DIFFICULTY.hard);
        },
    };
})(typeof window !== 'undefined' ? window : this);
