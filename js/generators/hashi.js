/**
 * Hashi (Hashiwokakero / Bridges) — generator + logic solver.
 *
 * A Hashi puzzle is a set of numbered "islands" on a grid. The player draws
 * bridges between islands so that:
 *   • bridges run only horizontally or vertically between two islands that are
 *     the nearest island to each other along that row/column (a clear corridor);
 *   • each pair of islands carries 0, 1 or 2 bridges;
 *   • bridges never cross each other (a horizontal and a vertical bridge can't
 *     occupy the same cell);
 *   • every island's bridge count equals its number;
 *   • all islands form a single connected network.
 * A well-formed puzzle has exactly one solution.
 *
 * Design — an edge CSP
 * --------------------
 * The candidate bridges are the edges between consecutive islands in each row
 * and column. Each edge carries an integer 0..2. The solver keeps per-edge
 * bounds [lo,hi] and propagates three rule families to a fixpoint:
 *   1. degree   — an island's incident edges must sum to its number;
 *   2. crossing — two perpendicular edges that intersect can't both be >0;
 *   3. connectivity — the "still-possible" graph (edges with hi>=1) must stay
 *      connected, and any cut edge of it is forced to >=1.
 * If propagation alone finishes the board it is uniquely solvable (it never
 * branched). Difficulty bands on how much trial reasoning is needed on top.
 *
 * Exposed:
 *   window.PuzzleGenerators.hashi(size, difficulty, seed, onProgress)
 *     → { id, game:'hashi', size, difficulty, islands:[{r,c,need}],
 *         solution:[{a,b,v}], stats }
 *   window.PuzzleSolvers.hashi  — { buildGraph, propagate, solve, countSolutions,
 *                                   verify, nextStep, nextStepDeep, UNKNOWN }
 *   window.PuzzleGenerators.hashiInternals — for the self-test
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    // -----------------------------------------------------------------
    // Graph model — islands + candidate edges (consecutive aligned pairs)
    // -----------------------------------------------------------------

    /** Build the candidate-bridge graph for a set of islands on an N×N grid.
     *  islands: [{r,c,need}]. Returns
     *    { N, islands, edges:[{a,b,dir,cells}], incident:[[e...]], cross:[[e...]] }
     *  where an edge joins two islands adjacent along a row/column with a clear
     *  corridor between them, `cells` is the exclusive corridor, and `cross[e]`
     *  lists edges whose corridor geometrically intersects e's. */
    function buildGraph(N, islands) {
        const m = islands.length;
        const at = new Int32Array(N * N).fill(-1);
        for (let i = 0; i < m; i++) at[islands[i].r * N + islands[i].c] = i;
        const edges = [];
        const incident = Array.from({ length: m }, () => []);
        const byRow = new Map(), byCol = new Map();
        for (let i = 0; i < m; i++) {
            const { r, c } = islands[i];
            (byRow.get(r) || byRow.set(r, []).get(r)).push(i);
            (byCol.get(c) || byCol.set(c, []).get(c)).push(i);
        }
        const addEdge = (a, b, dir, cells) => {
            const e = edges.length;
            edges.push({ a, b, dir, cells });
            incident[a].push(e); incident[b].push(e);
        };
        for (const arr of byRow.values()) {
            arr.sort((x, y) => islands[x].c - islands[y].c);
            for (let k = 1; k < arr.length; k++) {
                const a = arr[k - 1], b = arr[k], r = islands[a].r;
                const c1 = islands[a].c, c2 = islands[b].c;
                if (c2 - c1 < 2) continue; // adjacent islands with no gap: no bridge
                const cells = [];
                for (let c = c1 + 1; c < c2; c++) cells.push(r * N + c);
                addEdge(a, b, 'H', cells);
            }
        }
        for (const arr of byCol.values()) {
            arr.sort((x, y) => islands[x].r - islands[y].r);
            for (let k = 1; k < arr.length; k++) {
                const a = arr[k - 1], b = arr[k], c = islands[a].c;
                const r1 = islands[a].r, r2 = islands[b].r;
                if (r2 - r1 < 2) continue;
                const cells = [];
                for (let r = r1 + 1; r < r2; r++) cells.push(r * N + c);
                addEdge(a, b, 'V', cells);
            }
        }
        // Crossings: a horizontal edge and a vertical edge cross iff they share a
        // corridor cell.
        const cellToEdges = new Map();
        for (let e = 0; e < edges.length; e++) for (const cell of edges[e].cells) {
            (cellToEdges.get(cell) || cellToEdges.set(cell, []).get(cell)).push(e);
        }
        const cross = Array.from({ length: edges.length }, () => []);
        for (const list of cellToEdges.values()) {
            if (list.length < 2) continue;
            for (let i = 0; i < list.length; i++) for (let j = i + 1; j < list.length; j++) {
                const e = list[i], f = list[j];
                if (edges[e].dir !== edges[f].dir) {
                    if (!cross[e].includes(f)) cross[e].push(f);
                    if (!cross[f].includes(e)) cross[f].push(e);
                }
            }
        }
        return { N, islands, edges, incident, cross, at };
    }

    const UNKNOWN = -1;

    // -----------------------------------------------------------------
    // Propagation
    // -----------------------------------------------------------------

    /** Union-find helper over island count m. */
    function makeDSU(m) {
        const p = new Int32Array(m);
        for (let i = 0; i < m; i++) p[i] = i;
        const find = (x) => { while (p[x] !== x) { p[x] = p[p[x]]; x = p[x]; } return x; };
        return { find, union: (a, b) => { a = find(a); b = find(b); if (a !== b) p[a] = b; } };
    }

    /** Is the "possible" graph (edges with hi>=1) connected across all islands? */
    function possibleConnected(G, hi) {
        const m = G.islands.length;
        if (m <= 1) return true;
        const dsu = makeDSU(m);
        for (let e = 0; e < G.edges.length; e++) if (hi[e] >= 1) dsu.union(G.edges[e].a, G.edges[e].b);
        const r0 = dsu.find(0);
        for (let i = 1; i < m; i++) if (dsu.find(i) !== r0) return false;
        return true;
    }

    /** Cut edges (bridges) of the possible graph — edges with hi>=1 whose removal
     *  would disconnect it. Such an edge must carry at least one bridge. Returns
     *  a boolean array over edges. (Tarjan bridge-finding on the possible graph.) */
    function cutEdges(G, hi) {
        const m = G.islands.length;
        const adj = Array.from({ length: m }, () => []); // [ [nbr, edgeIndex] ]
        for (let e = 0; e < G.edges.length; e++) if (hi[e] >= 1) {
            adj[G.edges[e].a].push([G.edges[e].b, e]);
            adj[G.edges[e].b].push([G.edges[e].a, e]);
        }
        const disc = new Int32Array(m).fill(-1), low = new Int32Array(m);
        const isCut = new Uint8Array(G.edges.length);
        let timer = 0;
        // Iterative DFS to avoid stack limits on large boards.
        const stack = [];
        for (let s = 0; s < m; s++) {
            if (disc[s] !== -1) continue;
            stack.push([s, -1, 0]);
            while (stack.length) {
                const frame = stack[stack.length - 1];
                const [u, pe, ip] = frame;
                if (ip === 0) { disc[u] = low[u] = timer++; }
                if (ip < adj[u].length) {
                    frame[2]++;
                    const [w, e] = adj[u][ip];
                    if (e === pe) continue;
                    if (disc[w] === -1) stack.push([w, e, 0]);
                    else low[u] = Math.min(low[u], disc[w]);
                } else {
                    stack.pop();
                    if (stack.length) {
                        const par = stack[stack.length - 1];
                        const pu = par[0];
                        low[pu] = Math.min(low[pu], low[u]);
                        if (low[u] > disc[pu]) isCut[pe] = 1;
                    }
                }
            }
        }
        return isCut;
    }

    /** Propagate the three rule families to a fixpoint. Mutates lo/hi.
     *  Returns false on contradiction. `conn` toggles the (pricier) connectivity
     *  rules so a weaker solver can model shallower reasoning. */
    function propagate(G, needs, lo, hi, conn) {
        const useConn = conn !== false;
        let changed = true, passes = 0;
        while (changed) {
            changed = false; passes++;
            // (1) degree
            for (let v = 0; v < G.islands.length; v++) {
                const inc = G.incident[v];
                let sumLo = 0, sumHi = 0;
                for (const e of inc) { sumLo += lo[e]; sumHi += hi[e]; }
                const need = needs[v];
                if (need < sumLo || need > sumHi) return false;
                for (const e of inc) {
                    const nlo = Math.max(lo[e], need - (sumHi - hi[e]));
                    const nhi = Math.min(hi[e], need - (sumLo - lo[e]));
                    if (nlo > nhi) return false;
                    if (nlo > lo[e]) { lo[e] = nlo; changed = true; }
                    if (nhi < hi[e]) { hi[e] = nhi; changed = true; }
                }
            }
            // (2) crossing — a committed bridge forbids every edge it crosses
            for (let e = 0; e < G.edges.length; e++) if (lo[e] >= 1) {
                for (const f of G.cross[e]) {
                    if (lo[f] >= 1) return false;
                    if (hi[f] !== 0) { hi[f] = 0; changed = true; }
                }
            }
            if (useConn) {
                // (3a) the possible graph must stay connected
                if (!possibleConnected(G, hi)) return false;
                // (3b) any cut edge of the possible graph must carry a bridge
                const isCut = cutEdges(G, hi);
                for (let e = 0; e < G.edges.length; e++) if (isCut[e] && lo[e] < 1) {
                    if (hi[e] < 1) return false;
                    lo[e] = 1; changed = true;
                }
            }
        }
        return true;
    }

    // -----------------------------------------------------------------
    // Full solver / solution counter
    // -----------------------------------------------------------------

    /** Count solutions up to `cap` (stops early). Returns { count, sol } where
     *  `sol` is the edge-value array of the first solution found (or null). */
    function countSolutions(G, needs, cap, conn) {
        const E = G.edges.length;
        let count = 0, firstSol = null, nodes = 0;
        const budget = 200000;
        const lo0 = new Int8Array(E), hi0 = new Int8Array(E).fill(2);
        function leafValid(lo) {
            // all decided (lo==hi guaranteed by caller); check connectivity of the
            // actual bridge graph (edges with value>=1).
            const dsu = makeDSU(G.islands.length);
            for (let e = 0; e < E; e++) if (lo[e] >= 1) dsu.union(G.edges[e].a, G.edges[e].b);
            const r0 = dsu.find(0);
            for (let i = 1; i < G.islands.length; i++) if (dsu.find(i) !== r0) return false;
            return true;
        }
        function rec(lo, hi) {
            if (count >= cap) return;
            if (++nodes > budget) { count = -1; return; }
            const l = lo.slice(), h = hi.slice();
            if (!propagate(G, needs, l, h, conn)) return;
            let be = -1;
            for (let e = 0; e < E; e++) if (l[e] !== h[e]) { be = e; break; }
            if (be === -1) {
                if (leafValid(l)) { count++; if (!firstSol) firstSol = l.slice(); }
                return;
            }
            for (let v = l[be]; v <= h[be]; v++) {
                const l2 = l.slice(), h2 = h.slice();
                l2[be] = v; h2[be] = v;
                rec(l2, h2);
                if (count >= cap || count < 0) return;
            }
        }
        rec(lo0, hi0);
        return { count, sol: firstSol };
    }

    // -----------------------------------------------------------------
    // Difficulty-tier solving (pure propagation vs 1-level trial)
    // -----------------------------------------------------------------

    /** Try to solve from empty by pure propagation only. Returns
     *  { solved, lo, hi, passes } — solved iff every edge got decided. */
    function solveProp(G, needs, conn) {
        const E = G.edges.length;
        const lo = new Int8Array(E), hi = new Int8Array(E).fill(2);
        if (!propagate(G, needs, lo, hi, conn)) return { solved: false, lo, hi };
        let solved = true;
        for (let e = 0; e < E; e++) if (lo[e] !== hi[e]) { solved = false; break; }
        return { solved, lo, hi };
    }

    /** One depth-1 trial pass from the current bounds: for each undecided edge,
     *  test every candidate value and keep only the feasible ones, tightening the
     *  [lo,hi] window to the feasible range. Returns the number of bounds moved. */
    function trialPass(G, needs, lo, hi, conn) {
        const E = G.edges.length;
        let gained = 0;
        for (let e = 0; e < E; e++) {
            if (lo[e] === hi[e]) continue;
            let flo = 3, fhi = -1;
            for (let v = lo[e]; v <= hi[e]; v++) {
                const l = lo.slice(), h = hi.slice();
                l[e] = v; h[e] = v;
                if (propagate(G, needs, l, h, conn)) { if (v < flo) flo = v; if (v > fhi) fhi = v; }
            }
            if (fhi < flo) return -1; // no feasible value → contradiction
            if (flo > lo[e]) { lo[e] = flo; gained++; }
            if (fhi < hi[e]) { hi[e] = fhi; gained++; }
        }
        return gained;
    }

    /** Solve with a given trial depth (0 = pure prop, 1 = prop + trial passes).
     *  Returns true iff fully decided. */
    function solvesBy(G, needs, depth, conn) {
        const E = G.edges.length;
        const lo = new Int8Array(E), hi = new Int8Array(E).fill(2);
        if (!propagate(G, needs, lo, hi, conn)) return false;
        let guard = 0;
        for (;;) {
            let done = true;
            for (let e = 0; e < E; e++) if (lo[e] !== hi[e]) { done = false; break; }
            if (done) return true;
            if (depth < 1) return false;
            if (++guard > E * 4) return false;
            const g = trialPass(G, needs, lo, hi, conn);
            if (g <= 0) return false; // no progress or contradiction
            if (!propagate(G, needs, lo, hi, conn)) return false;
        }
    }

    // -----------------------------------------------------------------
    // Hints
    // -----------------------------------------------------------------

    /** Next forced edge by pure propagation from the player's state `cur`
     *  (edge-value array, UNKNOWN=-1 for undrawn, else 0..2 the player set).
     *  Returns { edge, value, reason } for an edge the player hasn't yet fixed to
     *  that value, or null. `reason` ∈ {degree, cross, cut}. */
    function nextStep(G, needs, cur) {
        const E = G.edges.length;
        const lo = new Int8Array(E), hi = new Int8Array(E).fill(2);
        for (let e = 0; e < E; e++) if (cur[e] !== UNKNOWN) { lo[e] = cur[e]; hi[e] = cur[e]; }
        if (!propagate(G, needs, lo, hi, true)) return null;
        for (let e = 0; e < E; e++) {
            if (lo[e] === hi[e] && cur[e] !== lo[e]) {
                return { edge: e, value: lo[e], reason: reasonFor(G, needs, cur, e, lo[e]) };
            }
        }
        return null;
    }

    /** Classify (roughly) why edge e is forced to `val` from state `cur`, for the
     *  hint banner: 'degree' (an island's count forces it), 'cross' (a committed
     *  perpendicular bridge rules it out), or 'cut' (connectivity needs it). */
    function reasonFor(G, needs, cur, e, val) {
        const E = G.edges.length;
        const lo = new Int8Array(E), hi = new Int8Array(E).fill(2);
        for (let k = 0; k < E; k++) if (cur[k] !== UNKNOWN) { lo[k] = cur[k]; hi[k] = cur[k]; }
        // crossing: val 0 and some crossing edge already committed >0
        if (val === 0) {
            for (const f of G.cross[e]) if (lo[f] >= 1) return 'cross';
        }
        // connectivity: val>=1 and e is a cut edge of the possible graph
        if (val >= 1) {
            propagate(G, needs, lo, hi, true);
            // recompute possible graph ignoring e → disconnected?
            const hi2 = hi.slice(); hi2[e] = 0;
            if (!possibleConnected(G, hi2)) return 'cut';
        }
        return 'degree';
    }

    /** Depth-1 refutation hint: find an undecided edge whose one value leads to a
     *  contradiction, so the other is forced. Returns
     *  { edge, value, assume:{edge,value} } (value = the forced one) or null. */
    function nextStepDeep(G, needs, cur) {
        const E = G.edges.length;
        const base = { lo: new Int8Array(E), hi: new Int8Array(E).fill(2) };
        for (let e = 0; e < E; e++) if (cur[e] !== UNKNOWN) { base.lo[e] = cur[e]; base.hi[e] = cur[e]; }
        if (!propagate(G, needs, base.lo, base.hi, true)) return null;
        for (let e = 0; e < E; e++) {
            if (base.lo[e] === base.hi[e]) continue;
            const feas = [];
            let badV = -1;
            for (let v = base.lo[e]; v <= base.hi[e]; v++) {
                const l = base.lo.slice(), h = base.hi.slice();
                l[e] = v; h[e] = v;
                if (propagate(G, needs, l, h, true)) feas.push(v);
                else if (badV < 0) badV = v;
            }
            // A clean one-step deduction: ruling out the impossible value(s) leaves
            // exactly one feasible value for this edge.
            if (feas.length === 1 && badV >= 0) return { edge: e, value: feas[0], assume: { edge: e, value: badV } };
        }
        return null;
    }

    /** Verify a player's full edge-value array solves the puzzle. */
    function verify(G, needs, vals) {
        const E = G.edges.length;
        for (let e = 0; e < E; e++) if (vals[e] < 0 || vals[e] > 2) return false;
        for (let v = 0; v < G.islands.length; v++) {
            let s = 0; for (const e of G.incident[v]) s += vals[e];
            if (s !== needs[v]) return false;
        }
        for (let e = 0; e < E; e++) if (vals[e] >= 1) for (const f of G.cross[e]) if (vals[f] >= 1) return false;
        const dsu = makeDSU(G.islands.length);
        for (let e = 0; e < E; e++) if (vals[e] >= 1) dsu.union(G.edges[e].a, G.edges[e].b);
        const r0 = dsu.find(0);
        for (let i = 1; i < G.islands.length; i++) if (dsu.find(i) !== r0) return false;
        return true;
    }

    // -----------------------------------------------------------------
    // Generator — grow a connected, non-crossing network, derive numbers
    // -----------------------------------------------------------------

    const DIFFS = {
        easy:   { depth: 0, density: 0.14, doubleFrac: 0.30 },
        medium: { depth: 0, density: 0.17, doubleFrac: 0.45 },
        hard:   { depth: 1, density: 0.18, doubleFrac: 0.55 },
    };

    /** Grow a random solution network on an N×N grid. Returns
     *  { islands:[{r,c}], bridges:[{a,b,v}] } with islands connected, bridges
     *  non-crossing, and no island sitting on a bridge corridor. */
    function growNetwork(N, rng, cfg) {
        const at = new Int32Array(N * N).fill(-1); // cell → island index
        const occupied = new Uint8Array(N * N);    // bridge corridor cells
        const islands = [];
        const bridges = [];
        const place = (r, c) => { const i = islands.length; islands.push({ r, c }); at[r * N + c] = i; return i; };

        // seed near the middle
        place((N >> 1), (N >> 1));
        const target = Math.max(4, Math.round(N * N * cfg.density));
        const DIRS = [[-1, 0], [1, 0], [0, -1], [0, 1]];
        let guard = 0, cap = target * 60;

        while (islands.length < target && guard++ < cap) {
            const src = PC.rng.pickInt(rng, 0, islands.length);
            const { r, c } = islands[src];
            const d = DIRS[PC.rng.pickInt(rng, 0, 4)];
            const dist = PC.rng.pickInt(rng, 2, Math.min(5, N)); // ≥2 so there's a gap
            const nr = r + d[0] * dist, nc = c + d[1] * dist;
            if (nr < 0 || nr >= N || nc < 0 || nc >= N) continue;
            if (at[nr * N + nc] !== -1) continue;        // cell taken by an island
            // corridor must be clear: no island, no existing bridge, no occupied
            let clear = true;
            const cells = [];
            for (let s = 1; s < dist; s++) {
                const cr = r + d[0] * s, cc = c + d[1] * s, id = cr * N + cc;
                if (at[id] !== -1 || occupied[id]) { clear = false; break; }
                cells.push(id);
            }
            if (!clear) continue;
            // new island can't sit where a perpendicular bridge already passes
            if (occupied[nr * N + nc]) continue;
            const v = rng() < cfg.doubleFrac ? 2 : 1;
            const b = place(nr, nc);
            bridges.push({ a: src, b, v });
            for (const id of cells) occupied[id] = 1;
        }

        // Add a few extra bridges between already-aligned islands (no new islands)
        // to enrich the numbers, keeping non-crossing + capacity ≤2 and need ≤8.
        const G0 = buildGraph(N, islands.map((p) => ({ r: p.r, c: p.c, need: 0 })));
        const val = new Int8Array(G0.edges.length);
        for (const br of bridges) {
            const e = G0.edges.findIndex((ed) => (ed.a === br.a && ed.b === br.b) || (ed.a === br.b && ed.b === br.a));
            if (e >= 0) val[e] = br.v;
        }
        const extraTries = Math.round(G0.edges.length * 0.4);
        const needOf = (i) => { let s = 0; for (const e of G0.incident[i]) s += val[e]; return s; };
        for (let t = 0; t < extraTries; t++) {
            const e = PC.rng.pickInt(rng, 0, G0.edges.length);
            if (val[e] >= 2) continue;
            const { a, b } = G0.edges[e];
            if (needOf(a) >= 8 || needOf(b) >= 8) continue;
            let crosses = false;
            for (const f of G0.cross[e]) if (val[f] >= 1) { crosses = true; break; }
            if (crosses) continue;
            val[e]++;
        }
        const outBridges = [];
        for (let e = 0; e < G0.edges.length; e++) if (val[e] >= 1) outBridges.push({ a: G0.edges[e].a, b: G0.edges[e].b, v: val[e] });
        return { islands: islands.map((p) => ({ r: p.r, c: p.c })), bridges: outBridges };
    }

    function attemptsFor(N) { return N <= 9 ? 160 : N <= 13 ? 120 : 90; }

    async function generate(size, difficulty, seed, onProgress) {
        const N = size;
        const rng = PC.rng.make(seed >>> 0);
        const cfg = DIFFS[difficulty] || DIFFS.medium;
        const attempts = attemptsFor(N);
        if (onProgress) await onProgress(0.03);

        const pool = [];
        for (let t = 0; t < attempts; t++) {
            const net = growNetwork(N, rng, cfg);
            if (net.islands.length < 4 || net.bridges.length < 3) continue;
            const needs = net.islands.map(() => 0);
            const islands = net.islands.map((p) => ({ r: p.r, c: p.c, need: 0 }));
            const G = buildGraph(N, islands);
            // derive needs from the grown solution
            const solVal = new Int8Array(G.edges.length);
            for (const br of net.bridges) {
                const e = G.edges.findIndex((ed) => (ed.a === br.a && ed.b === br.b) || (ed.a === br.b && ed.b === br.a));
                if (e >= 0) solVal[e] = br.v;
            }
            for (let v = 0; v < islands.length; v++) { let s = 0; for (const e of G.incident[v]) s += solVal[e]; islands[v].need = s; needs[v] = s; }
            if (needs.some((n) => n === 0)) continue; // every island must need ≥1
            if (!verify(G, needs, solVal)) continue;  // sanity: grown net is valid
            // uniqueness
            const { count } = countSolutions(G, needs, 2, true);
            if (count !== 1) continue;
            // difficulty gate: easy/medium must be pure-propagation solvable
            // (tier 0); hard must be depth-1 solvable (tier 0 or 1) but never
            // need blind search (tier 2).
            const tier0 = solvesBy(G, needs, 0, true);
            const tier = tier0 ? 0 : (solvesBy(G, needs, 1, true) ? 1 : 2);
            if (cfg.depth === 0 ? tier !== 0 : tier === 2) continue;
            pool.push({ islands, needs, solVal, G, tier, m: islands.length, bridges: net.bridges.length });
            if (onProgress && (t & 7) === 0) await onProgress(0.03 + 0.9 * (t + 1) / attempts);
            // stop early once we have enough of the right flavour
            if (difficulty === 'hard' && tier === 1 && pool.filter((p) => p.tier === 1).length >= 6) break;
            if (difficulty !== 'hard' && pool.length >= 10) break;
        }

        if (onProgress) await onProgress(0.96);
        if (!pool.length) {
            // Degenerate fallback: a tiny deterministic board (never blank).
            return fallback(N, difficulty, seed);
        }

        // Select by difficulty.
        let chosen;
        if (difficulty === 'hard') {
            const deep = pool.filter((p) => p.tier === 1);
            const use = (deep.length ? deep : pool).sort((a, b) => a.m - b.m);
            chosen = use[use.length - 1];
        } else {
            // prefer more islands for medium; fewer/shallower for easy
            pool.sort((a, b) => a.m - b.m);
            chosen = difficulty === 'easy' ? pool[0] : pool[Math.floor((pool.length - 1) / 2)];
        }

        const solution = [];
        for (let e = 0; e < chosen.G.edges.length; e++) if (chosen.solVal[e] >= 1) {
            solution.push({ a: chosen.G.edges[e].a, b: chosen.G.edges[e].b, v: chosen.solVal[e] });
        }
        if (onProgress) await onProgress(1);
        return {
            id: `hashi-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'hashi', size: N, difficulty,
            islands: chosen.islands.map((p) => ({ r: p.r, c: p.c, need: p.need })),
            solution,
            stats: { islands: chosen.m, bridges: chosen.bridges, tier: chosen.tier, poolSize: pool.length },
        };
    }

    function fallback(N, difficulty, seed) {
        // A 2×2 block of islands forming a square loop — always valid & unique.
        const a = 1, b = Math.min(N - 2, 4);
        const islands = [
            { r: a, c: a, need: 2 }, { r: a, c: b, need: 2 },
            { r: b, c: a, need: 2 }, { r: b, c: b, need: 2 },
        ];
        const G = buildGraph(N, islands);
        return {
            id: `hashi-${N}x${N}-${difficulty}-fallback`,
            game: 'hashi', size: N, difficulty,
            islands,
            solution: [{ a: 0, b: 1, v: 1 }, { a: 0, b: 2, v: 1 }, { a: 1, b: 3, v: 1 }, { a: 2, b: 3, v: 1 }],
            stats: { islands: 4, bridges: 4, tier: 0, poolSize: 0, fallback: true },
        };
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleGenerators.hashi = generate;
    global.PuzzleSolvers.hashi = { buildGraph, propagate, countSolutions, verify, nextStep, nextStepDeep, solvesBy, UNKNOWN };
    global.PuzzleGenerators.hashiInternals = {
        buildGraph, propagate, countSolutions, solveProp, solvesBy, trialPass, verify,
        nextStep, nextStepDeep, growNetwork, attemptsFor, possibleConnected, cutEdges, DIFFS, UNKNOWN,
    };
})(typeof window !== 'undefined' ? window : this);
