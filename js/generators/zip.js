/**
 * Zip — puzzle generator.
 *
 * A Zip puzzle is a single path from checkpoint 1 to checkpoint K that covers
 * every cell exactly once, visits the checkpoints in numeric order, and never
 * crosses a wall — i.e. a Hamiltonian path on the grid graph (minus walled
 * edges) with fixed endpoints and ordered waypoints.
 *
 * Approach (from the reference design + improvements):
 *   1. Sample a random FULL Hamiltonian path (backbite) — the solution.
 *   2. Uniqueness by ELIMINATION: any alternative solution P' differs from P
 *      by a set of "alternating cycles" (P XOR P'). Instead of proving
 *      uniqueness by exhaustive search, we repeatedly FIND alternatives, then
 *      break a whole batch of them at once with a greedy hitting-set of
 *      constraints (walls on edges an alternative uses but P doesn't, or
 *      checkpoints an alternative would visit out of order). Adding those
 *      constraints makes the board progressively DEDUCIBLE, so the leftover
 *      uniqueness check the forced-move solver does is cheap.
 *   3. Difficulty comes from the checkpoint-vs-wall mix + best-of-K on a
 *      branch-count (reasoning-depth) score.
 *
 * The forced-move edge solver (degree + no-cycle + checkpoint-order +
 * connectivity propagation, then bounded branching) both finds alternatives
 * and confirms final uniqueness; it was cross-validated against an independent
 * cell-based counter.
 *
 * Exposed via `window.PuzzleGenerators.zip(size, difficulty, seed, onProgress)`
 * → { id, game:'zip', size:N, difficulty, holes:[], walls, checkpoints, solution }.
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;
    const DEBUG = typeof location !== 'undefined' && /[?&]zip_debug=1\b/.test(location.search); // [DEBUG-HOOK]

    // -----------------------------------------------------------------
    // Grid / edge helpers  (cell id = r*N + c)
    // -----------------------------------------------------------------

    const rowOf = (id, N) => Math.floor(id / N);
    const colOf = (id, N) => id % N;
    const idOf = (r, c, N) => r * N + c;
    const EK = 1 << 16;
    const edgeKey = (a, b) => (a < b ? a * EK + b : b * EK + a);
    function edgeToCells(key, N) {
        const a = Math.floor(key / EK), b = key % EK;
        return [[rowOf(a, N), colOf(a, N)], [rowOf(b, N), colOf(b, N)]];
    }

    function buildAdj(N) {
        const adj = new Array(N * N);
        for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
            const id = idOf(r, c, N), a = [];
            if (r > 0) a.push(id - N);
            if (r < N - 1) a.push(id + N);
            if (c > 0) a.push(id - 1);
            if (c < N - 1) a.push(id + 1);
            adj[id] = a;
        }
        return adj;
    }

    // Cached edge model: edge↔cell incidence.
    let EMODEL = { N: 0 };
    function edgeModel(N) {
        if (EMODEL.N === N) return EMODEL;
        const HN = N * (N - 1), E = HN + (N - 1) * N;
        const eU = new Int32Array(E), eV = new Int32Array(E);
        const inc = new Int32Array(N * N * 4).fill(-1), incCnt = new Int32Array(N * N);
        const Hi = (r, c) => r * (N - 1) + c;
        const Vi = (r, c) => HN + r * N + c;
        for (let r = 0; r < N; r++) for (let c = 0; c < N - 1; c++) { const e = Hi(r, c); eU[e] = r * N + c; eV[e] = r * N + c + 1; }
        for (let r = 0; r < N - 1; r++) for (let c = 0; c < N; c++) { const e = Vi(r, c); eU[e] = r * N + c; eV[e] = (r + 1) * N + c; }
        const push = (cell, e) => { inc[cell * 4 + incCnt[cell]++] = e; };
        for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
            const id = r * N + c;
            if (c > 0) push(id, Hi(r, c - 1));
            if (c < N - 1) push(id, Hi(r, c));
            if (r > 0) push(id, Vi(r - 1, c));
            if (r < N - 1) push(id, Vi(r, c));
        }
        EMODEL = { N, E, eU, eV, inc, incCnt, Hi, Vi };
        return EMODEL;
    }

    function keyToEdge(key, N, model) {
        const a = Math.floor(key / EK), b = key % EK;
        return b === a + 1 ? model.Hi(rowOf(a, N), colOf(a, N)) : model.Vi(rowOf(a, N), colOf(a, N));
    }
    const edgeIndexToKey = (e, model) => edgeKey(model.eU[e], model.eV[e]);

    // -----------------------------------------------------------------
    // Random full Hamiltonian path via backbite
    // -----------------------------------------------------------------

    function snakePath(N) {
        const path = [];
        for (let r = 0; r < N; r++) {
            if (r % 2 === 0) for (let c = 0; c < N; c++) path.push(idOf(r, c, N));
            else for (let c = N - 1; c >= 0; c--) path.push(idOf(r, c, N));
        }
        return path;
    }
    function reverseSeg(path, pos, i, j) {
        while (i < j) { const a = path[i], b = path[j]; path[i] = b; path[j] = a; pos[b] = i; pos[a] = j; i++; j--; }
    }
    function randomHamPath(N, rng, adj) {
        const M = N * N;
        const path = snakePath(N);
        const pos = new Int32Array(M);
        for (let i = 0; i < M; i++) pos[path[i]] = i;
        const iters = Math.max(1000, 20 * M);
        for (let it = 0; it < iters; it++) {
            const useTail = rng() < 0.5;
            const end = useTail ? path[M - 1] : path[0];
            const nbrs = adj[end];
            const w = nbrs[PC.rng.pickInt(rng, 0, nbrs.length)];
            const k = pos[w];
            if (useTail) { if (k >= M - 2) continue; reverseSeg(path, pos, k + 1, M - 1); }
            else { if (k <= 1) continue; reverseSeg(path, pos, 0, k - 1); }
        }
        return path;
    }

    // -----------------------------------------------------------------
    // Forced-move edge solver (finds solutions / confirms uniqueness)
    // -----------------------------------------------------------------

    function analyzeEdges(N, model, wallSet, cpNum, cp1, cpK, K, cap, budget, collect, rules) {
        // rules: which forced-move deductions the solver may use. Full strength
        // (all true) is used for the uniqueness guarantee; a weaker set models
        // human-level reasoning and its branch count scores difficulty.
        const useOrder = !rules || rules.order !== false;
        const useConn = !rules || rules.conn !== false;
        const M = N * N;
        const { E, eU, eV, inc, incCnt } = model;
        const reqDeg = new Uint8Array(M).fill(2);
        reqDeg[cp1] = 1; reqDeg[cpK] = 1;
        const init = new Int8Array(E);
        for (const key of wallSet) init[keyToEdge(key, N, model)] = 2;

        const cpCells = [];
        for (let c = 0; c < M; c++) if (cpNum[c] !== 0) cpCells.push(c);
        const parent = new Int32Array(M), parent2 = new Int32Array(M);
        const find = (x) => { while (parent[x] !== x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; };
        const find2 = (x) => { while (parent2[x] !== x) { parent2[x] = parent2[parent2[x]]; x = parent2[x]; } return x; };
        const inQ = new Uint8Array(M);
        const q = [];
        const allCells = Int32Array.from({ length: M }, (_, i) => i);
        // ON-chain walk scratch for the monotonic checkpoint-order prune.
        const onNbr = new Int32Array(M * 2), onDeg = new Uint8Array(M), ovis = new Int32Array(M);
        let ogen = 0;

        let nodes = 0, aborted = false, count = 0, branches = 0;
        const solPaths = [];

        function propagate(s, seed) {
            q.length = 0;
            for (let i = 0; i < seed.length; i++) { const c = seed[i]; if (!inQ[c]) { inQ[c] = 1; q.push(c); } }
            let qh = 0;
            const contra = () => { inQ.fill(0); return 1; };
            for (;;) {
                while (qh < q.length) {
                    const cell = q[qh++]; inQ[cell] = 0;
                    const base = cell * 4, cnt = incCnt[cell];
                    let on = 0, unk = 0;
                    for (let i = 0; i < cnt; i++) { const st = s[inc[base + i]]; if (st === 1) on++; else if (st === 0) unk++; }
                    const need = reqDeg[cell];
                    if (on > need || unk < need - on) return contra();
                    const rem = need - on;
                    if (unk > 0 && (rem === 0 || unk === rem)) {
                        const val = rem === 0 ? 2 : 1;
                        for (let i = 0; i < cnt; i++) { const e = inc[base + i]; if (s[e] === 0) { s[e] = val; const o = eU[e] === cell ? eV[e] : eU[e]; if (!inQ[o]) { inQ[o] = 1; q.push(o); } } }
                    } else if (unk === 0 && on !== need) return contra();
                }
                let changed = false, bad = false;
                for (let i = 0; i < M; i++) parent[i] = i;
                for (let e = 0; e < E && !bad; e++) if (s[e] === 1) { const a = find(eU[e]), b = find(eV[e]); if (a === b) bad = true; else parent[a] = b; }
                if (bad) return contra();
                for (let e = 0; e < E; e++) if (s[e] === 0 && find(eU[e]) === find(eV[e])) {
                    s[e] = 2; changed = true;
                    if (!inQ[eU[e]]) { inQ[eU[e]] = 1; q.push(eU[e]); }
                    if (!inQ[eV[e]]) { inQ[eV[e]] = 1; q.push(eV[e]); }
                }
                if (useOrder && cpCells.length) {
                    // Walk each ON-chain; the checkpoint numbers on it must be a
                    // strictly monotonic run of consecutive integers (…i,i+1… or
                    // …i,i-1…). This prunes "order almost right" partials that
                    // the leaf check would otherwise only catch at the very end.
                    for (let i = 0; i < M; i++) onDeg[i] = 0;
                    for (let e = 0; e < E; e++) if (s[e] === 1) { const a = eU[e], b = eV[e]; onNbr[a * 2 + onDeg[a]++] = b; onNbr[b * 2 + onDeg[b]++] = a; }
                    const g = ++ogen;
                    for (let start = 0; start < M && !bad; start++) {
                        if (onDeg[start] > 1 || ovis[start] === g) continue;
                        let cur = start, prev = -1, lastCp = 0, dir = 0;
                        ovis[cur] = g;
                        for (;;) {
                            const n = cpNum[cur];
                            if (n !== 0) {
                                if (lastCp !== 0) { const d = n - lastCp; if (d !== 1 && d !== -1) { bad = true; break; } if (dir === 0) dir = d; else if (d !== dir) { bad = true; break; } }
                                lastCp = n;
                            }
                            let nxt = -1;
                            const base = cur * 2;
                            for (let i = 0; i < onDeg[cur]; i++) { const o = onNbr[base + i]; if (o !== prev) { nxt = o; break; } }
                            if (nxt === -1) break;
                            prev = cur; cur = nxt; ovis[cur] = g;
                        }
                    }
                    if (bad) return contra();
                }
                if (useConn) {
                    for (let i = 0; i < M; i++) parent2[i] = i;
                    for (let e = 0; e < E; e++) if (s[e] !== 2) { const a = find2(eU[e]), b = find2(eV[e]); if (a !== b) parent2[a] = b; }
                    const r0 = find2(0);
                    for (let i = 1; i < M; i++) if (find2(i) !== r0) return contra();
                }
                if (!changed) break;
            }
            for (let e = 0; e < E; e++) if (s[e] === 0) return 2;
            return 0;
        }

        // Walk the completed path from cp1; validate checkpoint order; return
        // the vertex sequence, or null if invalid.
        function leafPath(s) {
            let cur = cp1, prev = -1, cnt = 1, nextCp = 2;
            const seq = [cp1];
            for (;;) {
                let nxt = -1;
                const base = cur * 4, k = incCnt[cur];
                for (let i = 0; i < k; i++) { const e = inc[base + i]; if (s[e] === 1) { const o = eU[e] === cur ? eV[e] : eU[e]; if (o !== prev) { nxt = o; break; } } }
                if (nxt === -1) break;
                prev = cur; cur = nxt; cnt++; seq.push(cur);
                const n = cpNum[cur]; if (n !== 0) { if (n !== nextCp) return null; nextCp++; }
                if (cur === cpK) break;
            }
            if (cnt === M && cur === cpK && nextCp === K + 1) return seq;
            return null;
        }

        function search(s, seed) {
            if (aborted) return;
            if (++nodes > budget) { aborted = true; return; }
            const r = propagate(s, seed);
            if (r === 1) return;
            if (r === 0) { const seq = leafPath(s); if (seq) { count++; if (collect && solPaths.length < cap) solPaths.push(seq); } return; }
            let be = -1, bestUnk = 99;
            for (let cell = 0; cell < M && bestUnk > 2; cell++) {
                const base = cell * 4, cnt = incCnt[cell];
                let on = 0, unk = 0, anyE = -1;
                for (let i = 0; i < cnt; i++) { const e = inc[base + i], st = s[e]; if (st === 1) on++; else if (st === 0) { unk++; anyE = e; } }
                if (unk > 0 && on < reqDeg[cell] && unk < bestUnk) { bestUnk = unk; be = anyE; }
            }
            if (be === -1) { for (let e = 0; e < E; e++) if (s[e] === 0) { be = e; break; } }
            if (be === -1) return;
            branches++;
            const seed2 = [eU[be], eV[be]];
            const s1 = s.slice(); s1[be] = 1; search(s1, seed2); if (count >= cap || aborted) return;
            const s2 = s.slice(); s2[be] = 2; search(s2, seed2);
        }

        search(init, allCells);
        return { count: aborted ? -1 : count, aborted, branches, solPaths };
    }

    // -----------------------------------------------------------------
    // Uniqueness by elimination (walls) — greedy hitting-set of alternatives
    // -----------------------------------------------------------------

    const samePath = (a, b) => { if (a.length !== b.length) return false; for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false; return true; };

    /** Edge-index set of a vertex path. */
    function pathEdgeSet(path, N, model) {
        const s = new Set();
        for (let i = 1; i < path.length; i++) s.add(keyToEdge(edgeKey(path[i - 1], path[i]), N, model));
        return s;
    }

    /** Greedy hitting set: pick the fewest walls (from alternatives' P-absent
     *  edges) that break every listed alternative. */
    function pickBreakingWalls(alts, Pset, N, model) {
        const altEdges = alts.map((a) => {
            const s = [];
            for (let i = 1; i < a.length; i++) { const e = keyToEdge(edgeKey(a[i - 1], a[i]), N, model); if (!Pset.has(e)) s.push(e); }
            return s;
        });
        const remaining = new Set(alts.map((_, i) => i));
        const chosen = [];
        while (remaining.size) {
            const cnt = new Map();
            for (const i of remaining) for (const e of altEdges[i]) cnt.set(e, (cnt.get(e) || 0) + 1);
            let bestE = -1, bestC = 0;
            for (const [e, c] of cnt) if (c > bestC) { bestC = c; bestE = e; }
            if (bestE === -1) break;
            chosen.push(bestE);
            for (const i of [...remaining]) if (altEdges[i].includes(bestE)) remaining.delete(i);
        }
        return chosen;
    }

    /** Place `targetK` checkpoints along P (the two endpoints plus interior
     *  ones spread evenly with jitter), numbered by position on P. Returns
     *  { cpNum, K }. More anchors ⇒ fewer walls needed ⇒ easier. */
    function placeCheckpoints(P, targetK, rng, N) {
        const M = P.length;
        targetK = Math.max(2, Math.min(targetK, M));
        const idxSet = new Set([0, M - 1]);
        const need = targetK - 2;
        if (need > 0) {
            const step = (M - 1) / (targetK - 1);
            for (let i = 1; i <= need; i++) {
                let pos = Math.round(i * step) + (rng ? PC.rng.pickInt(rng, -1, 2) : 0);
                pos = Math.max(1, Math.min(M - 2, pos));
                while (idxSet.has(pos) && pos < M - 2) pos++;
                while (idxSet.has(pos) && pos > 1) pos--;
                idxSet.add(pos);
            }
        }
        const idxs = [...idxSet].sort((a, b) => a - b);
        const cpNum = new Int32Array(N * N);
        idxs.forEach((idx, i) => { cpNum[P[idx]] = i + 1; });
        return { cpNum, K: idxs.length };
    }

    /** Wall the board (only edges P never uses) until it is provably unique.
     *  Returns { ok, branches } (branches from the final proving solve). */
    function forceUnique(N, model, adj, wallSet, cpNum, cp1, cpK, K, P, budget, rng) {
        const Pset = pathEdgeSet(P, N, model);
        // non-solution edges, shuffled, for the rare "reduce ambiguity" fallback
        const nonSol = [];
        for (let a = 0; a < N * N; a++) for (const b of adj[a]) if (a < b) { const k = edgeKey(a, b); if (!Pset.has(keyToEdge(k, N, model))) nonSol.push(k); }
        if (rng) PC.rng.shuffle(nonSol, rng);
        // Finding alternatives to break is cheap; a full proof is only needed
        // once (and is tiny once the board is deducible), so cap each call.
        const findBudget = Math.min(budget, 12000);
        let np = 0, guard = 6 * N * N, lastBranches = 0;
        while (guard-- > 0) {
            const res = analyzeEdges(N, model, wallSet, cpNum, cp1, cpK, K, 6, findBudget, true);
            lastBranches = res.branches;
            const alts = res.solPaths.filter((pp) => !samePath(pp, P));
            if (alts.length === 0 && !res.aborted) return { ok: true, branches: res.branches };
            let added = false;
            if (alts.length > 0) {
                const walls = pickBreakingWalls(alts, Pset, N, model);
                for (const e of walls) { const k = edgeIndexToKey(e, model); if (!wallSet.has(k)) { wallSet.add(k); added = true; } }
            }
            if (!added) { // aborted with no usable alt (very open): shrink the space
                while (np < nonSol.length) { const k = nonSol[np++]; if (!wallSet.has(k)) { wallSet.add(k); added = true; break; } }
            }
            if (!added) return { ok: false, branches: lastBranches };
        }
        return { ok: false, branches: lastBranches };
    }

    // -----------------------------------------------------------------
    // Difficulty knobs (placeholder — refined after uniqueness verified)
    // -----------------------------------------------------------------

    // best-of-K pool size. Each candidate is cheap now (forceUnique is fast),
    // so we can sample several and pick by difficulty band.
    function attemptsFor(N) { return N <= 8 ? 14 : N <= 10 ? 9 : 5; }
    function proveBudget(N) { return 20000 + N * N * 300; }
    // Weak (human-level) solver: degree + no-cycle only. Its branch count on a
    // unique board scores difficulty (how much guessing without global
    // reasoning). Capped small: if it can't solve within this many nodes the
    // puzzle is simply "very hard" — no need to grind the full tree.
    // Human-level scorer: uses checkpoint order (obvious to players) + degree +
    // no-cycle, but NOT the global connectivity flood-fill (that's the harder
    // reasoning). Its branch count ⇒ how much guessing remains ⇒ difficulty.
    const WEAK = { order: true, conn: false };
    function weakBudget(N) { return 4000 + N * N * 60; }
    // Checkpoint count per tier (incl. the two endpoints). More checkpoints ⇒
    // more anchors ⇒ fewer walls ⇒ easier; the main difficulty lever.
    function cpCountFor(N, difficulty) {
        const M = N * N;
        if (difficulty === 'easy') return Math.max(5, Math.round(M * 0.25));
        if (difficulty === 'hard') return Math.max(3, Math.round(M * 0.05));
        return Math.max(4, Math.round(M * 0.15));                 // medium
    }

    // -----------------------------------------------------------------
    // Entry point. Difficulty lever = checkpoint density (easy = many numbered
    // anchors ⇒ easy connect-the-dots; hard = few ⇒ more path reasoning); walls
    // top up uniqueness. Within a tier, best-of-K picks a representative.
    // -----------------------------------------------------------------

    async function generate(size, difficulty, seed, onProgress) {
        const N = size, M = N * N;
        const rng = PC.rng.make(seed >>> 0);
        const adj = buildAdj(N);
        const model = edgeModel(N);
        const budget = proveBudget(N);
        const attempts = attemptsFor(N);
        const cpCount = cpCountFor(N, difficulty);
        if (onProgress) await onProgress(0.05);

        // best-of-K: each candidate is a fresh full path with pre-placed
        // checkpoints, made unique with walls, scored by the WEAK solver's
        // branch count. Ship by band: easy → least guessing, hard → most.
        const pool = [];
        for (let t = 0; t < attempts; t++) {
            const path = randomHamPath(N, rng, adj);
            const cp1 = path[0], cpK = path[M - 1];
            const { cpNum, K } = placeCheckpoints(path, cpCount, rng, N);
            const wallSet = new Set();
            const fu = forceUnique(N, model, adj, wallSet, cpNum, cp1, cpK, K, path, budget, rng);
            if (!fu.ok) continue;
            const w = analyzeEdges(N, model, wallSet, cpNum, cp1, cpK, K, 2, weakBudget(N), false, WEAK);
            pool.push({ path, cpNum, K, wallSet, score: w.aborted ? 1e9 : w.branches });
            if (onProgress) await onProgress(0.1 + 0.85 * (t + 1) / attempts);
        }
        if (!pool.length) { // extremely unlikely; ship one best-effort
            const path = randomHamPath(N, rng, adj);
            const cp1 = path[0], cpK = path[M - 1];
            const { cpNum, K } = placeCheckpoints(path, cpCount, rng, N);
            const wallSet = new Set();
            forceUnique(N, model, adj, wallSet, cpNum, cp1, cpK, K, path, budget * 3, rng);
            pool.push({ path, cpNum, K, wallSet, score: 0 });
        }
        pool.sort((a, b) => a.score - b.score);
        const idx = difficulty === 'easy' ? 0
            : difficulty === 'hard' ? pool.length - 1
                : Math.floor((pool.length - 1) / 2);
        const chosen = pool[idx];

        if (onProgress) await onProgress(1);

        const checkpoints = [];
        for (let c = 0; c < M; c++) { const n = chosen.cpNum[c]; if (n) checkpoints.push({ r: rowOf(c, N), c: colOf(c, N), n }); }
        checkpoints.sort((a, b) => a.n - b.n);
        const walls = [...chosen.wallSet].map((k) => edgeToCells(k, N));
        const solution = chosen.path.map((id) => [rowOf(id, N), colOf(id, N)]);
        if (DEBUG) {
            /* eslint-disable no-console */
            console.log(`[zip] N=${N} ${difficulty}: ${checkpoints.length} cps, ${walls.length} walls, score=${chosen.score}, pool=${pool.length}`);
            /* eslint-enable no-console */
        }
        return {
            id: `zip-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'zip', size: N, difficulty,
            holes: [], walls, checkpoints, solution,
        };
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.zip = generate;
    global.PuzzleGenerators.zipInternals = {   // [DEBUG-HOOK]
        buildAdj, edgeModel, randomHamPath, analyzeEdges, forceUnique,
        edgeKey, idOf, edgeToCells, keyToEdge, pathEdgeSet, attemptsFor, proveBudget,
    };
})(typeof window !== 'undefined' ? window : this);
