/**
 * Light Up (Akari) — generator + layered solver.
 *
 * Board: an N×N grid of WHITE cells and WALL cells. Some walls carry a number
 * 0–4 = how many of its orthogonally-adjacent white cells hold a bulb. Place
 * bulbs on white cells so that: every white cell is lit (a bulb shines across
 * its row/column until a wall/edge), no two bulbs see each other, and every
 * numbered wall's count is exact.
 *
 * Difficulty backbone (mirrors Nonogram's tiered idea):
 *   • Tier 1 — local propagation (number rules + visibility + coverage),
 *     iterated to a fixpoint. Everything it can derive is "basic".
 *   • Tier 2/3 — trial depth: when propagation stalls you must assume a cell,
 *     propagate, and force the opposite on contradiction. The minimum nesting
 *     depth needed (1, 2, …) is the hardness lever; propagation passes are a
 *     secondary depth signal.
 * A puzzle solvable by pure deduction within the depth cap has a UNIQUE
 * solution; the generator keeps only those and bands Easy/Medium/Hard by score.
 *
 * Exposed:
 *   window.PuzzleGenerators.guards(size, difficulty, seed, onProgress)
 *     → { id, game:'guards', size, difficulty, grid, solution, stats }
 *   window.PuzzleSolvers.guards       — { propagate, solveTier, countSolutions }
 *   window.PuzzleGenerators.guardsInternals — for the self-test
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    // Solver bulb-state for white cells.
    const UNKNOWN = 0, BULB = 1, NOBULB = 2;
    const MAX_TRIAL = 2; // deepest "assume & check" nesting we accept (keeps it fair)

    // Per-difficulty generation config:
    //   gateDepth — the trial depth the minimised board must stay solvable at
    //               (0 = pure propagation; 1 = may need one "assume→contradiction").
    //   zeroFrac  — how aggressively to strip 0-clues (scales with difficulty so
    //               Easy keeps more "free" 0s and Medium/Hard look clean).
    //   numFrac   — how aggressively to strip numbered clues.
    const DIFFS = {
        easy:   { gateDepth: 0, zeroFrac: 0.35, numFrac: 0.12 },
        medium: { gateDepth: 0, zeroFrac: 0.90, numFrac: 0.55 },
        hard:   { gateDepth: 1, zeroFrac: 1.00, numFrac: 1.00, maxChain: 4 },
    };

    const DIRS = [[-1, 0], [1, 0], [0, -1], [0, 1]];

    // -----------------------------------------------------------------
    // Layout context (fixed per wall layout; clue array is passed separately
    // so clue-minimisation can reuse the precomputed rays).
    // -----------------------------------------------------------------
    function makeCtx(N, wall) {
        const whites = [];
        for (let i = 0; i < N * N; i++) if (!wall[i]) whites.push(i);
        // rays[i] = white cells a bulb at i lights (its cross up to walls/edges).
        const rays = new Array(N * N);
        const wallNeigh = new Array(N * N);
        for (let i = 0; i < N * N; i++) {
            const r = (i / N) | 0, c = i % N;
            if (wall[i]) {
                const ns = [];
                for (const [dr, dc] of DIRS) {
                    const rr = r + dr, cc = c + dc;
                    if (rr >= 0 && rr < N && cc >= 0 && cc < N && !wall[rr * N + cc]) ns.push(rr * N + cc);
                }
                wallNeigh[i] = ns;
                continue;
            }
            const ray = [];
            for (const [dr, dc] of DIRS) {
                let rr = r + dr, cc = c + dc;
                while (rr >= 0 && rr < N && cc >= 0 && cc < N && !wall[rr * N + cc]) {
                    ray.push(rr * N + cc); rr += dr; cc += dc;
                }
            }
            rays[i] = ray;
        }
        // Scratch buffers reused across the (single-threaded, sequential) solver
        // calls so the hot propagation loop doesn't allocate per pass/trial.
        return { N, wall, rays, wallNeigh, whites, _lit: new Uint8Array(N * N), _trial: new Int8Array(N * N) };
    }

    // -----------------------------------------------------------------
    // Tier 1 — local propagation to a fixpoint.
    // Returns { ok, passes }. ok=false on contradiction. Mutates `b`.
    // -----------------------------------------------------------------
    function propagate(ctx, clue, b) {
        const { N, wall, rays, wallNeigh, whites } = ctx;
        let changed = true, passes = 0;
        while (changed) {
            changed = false; passes++;

            // (a) number constraints
            for (let i = 0; i < N * N; i++) {
                if (!wall[i] || clue[i] < 0) continue;
                const ns = wallNeigh[i];
                let nb = 0, nu = 0;
                for (const j of ns) { if (b[j] === BULB) nb++; else if (b[j] === UNKNOWN) nu++; }
                if (nb > clue[i] || nb + nu < clue[i]) return { ok: false, passes };
                if (nb === clue[i] && nu > 0) { for (const j of ns) if (b[j] === UNKNOWN) { b[j] = NOBULB; changed = true; } }
                else if (nb + nu === clue[i] && nu > 0) { for (const j of ns) if (b[j] === UNKNOWN) { b[j] = BULB; changed = true; } }
            }

            // (b) visibility: a definite bulb forbids bulbs along its sight-lines.
            for (const i of whites) {
                if (b[i] !== BULB) continue;
                for (const j of rays[i]) {
                    if (b[j] === BULB) return { ok: false, passes };
                    if (b[j] === UNKNOWN) { b[j] = NOBULB; changed = true; }
                }
            }

            // (c) coverage: every white cell must end up lit.
            const lit = ctx._lit; lit.fill(0);
            for (const i of whites) {
                if (b[i] === BULB) { lit[i] = 1; for (const j of rays[i]) lit[j] = 1; }
            }
            for (const i of whites) {
                if (lit[i]) continue;
                // candidates that could still light i: itself + its ray cells, if not ruled out.
                let only = -1, cnt = 0;
                if (b[i] !== NOBULB) { only = i; cnt++; }
                for (const j of rays[i]) { if (b[j] !== NOBULB) { only = j; cnt++; if (cnt > 1) break; } }
                if (cnt === 0) return { ok: false, passes };
                if (cnt === 1 && b[only] === UNKNOWN) { b[only] = BULB; changed = true; }
            }
        }
        return { ok: true, passes };
    }

    // A completed assignment satisfies every rule?
    function verify(ctx, clue, b) {
        const { N, wall, rays, wallNeigh, whites } = ctx;
        for (let i = 0; i < N * N; i++) {
            if (!wall[i] || clue[i] < 0) continue;
            let cnt = 0;
            for (const j of wallNeigh[i]) if (b[j] === BULB) cnt++;
            if (cnt !== clue[i]) return false;
        }
        const lit = new Uint8Array(N * N);
        for (const i of whites) {
            if (b[i] === BULB) {
                for (const j of rays[i]) { if (b[j] === BULB) return false; lit[j] = 1; }
                lit[i] = 1;
            }
        }
        for (const i of whites) if (!lit[i]) return false;
        return true;
    }

    function fullyAssigned(ctx, b) {
        for (const i of ctx.whites) if (b[i] === UNKNOWN) return false;
        return true;
    }

    // -----------------------------------------------------------------
    // Deductive solver with trial lookahead of `depth` (0 = propagation only).
    // Sound (never guesses): only sets a value when the opposite is proven
    // contradictory. Returns { ok } (ok=false on contradiction). Mutates `b`.
    // -----------------------------------------------------------------
    function deductiveSolve(ctx, clue, b, depth) {
        const p = propagate(ctx, clue, b);
        if (!p.ok) return { ok: false };
        if (depth <= 0) return { ok: true };
        let changed = true;
        while (changed) {
            changed = false;
            for (const i of ctx.whites) {
                if (b[i] !== UNKNOWN) continue;
                const t = b.slice(); t[i] = BULB;
                if (!deductiveSolve(ctx, clue, t, depth - 1).ok) {
                    b[i] = NOBULB;
                    if (!propagate(ctx, clue, b).ok) return { ok: false };
                    changed = true; continue;
                }
                const f = b.slice(); f[i] = NOBULB;
                if (!deductiveSolve(ctx, clue, f, depth - 1).ok) {
                    b[i] = BULB;
                    if (!propagate(ctx, clue, b).ok) return { ok: false };
                    changed = true; continue;
                }
            }
        }
        return { ok: true };
    }

    // Minimum trial depth (0..MAX_TRIAL) that fully + validly solves, else -1.
    // Also returns the tier-0 propagation pass count as a secondary signal.
    function solveTier(ctx, clue) {
        const base = new Int8Array(ctx.N * ctx.N);
        const passes = propagate(ctx, clue, base.slice()).passes;
        for (let d = 0; d <= MAX_TRIAL; d++) {
            const b = new Int8Array(ctx.N * ctx.N);
            const res = deductiveSolve(ctx, clue, b, d);
            if (res.ok && fullyAssigned(ctx, b) && verify(ctx, clue, b)) {
                return { solved: true, tier: d, passes };
            }
        }
        return { solved: false, tier: -1, passes };
    }

    // -----------------------------------------------------------------
    // Uniqueness: count solutions (propagation-pruned backtracking), up to cap.
    // -----------------------------------------------------------------
    function countSolutions(ctx, clue, cap) {
        let count = 0;
        (function rec(b0) {
            if (count >= cap) return;
            const b = b0.slice();
            if (!propagate(ctx, clue, b).ok) return;
            let pick = -1;
            for (const i of ctx.whites) if (b[i] === UNKNOWN) { pick = i; break; }
            if (pick < 0) { if (verify(ctx, clue, b)) count++; return; }
            const t = b.slice(); t[pick] = BULB; rec(t);
            if (count >= cap) return;
            const f = b.slice(); f[pick] = NOBULB; rec(f);
        })(new Int8Array(ctx.N * ctx.N));
        return count;
    }

    // -----------------------------------------------------------------
    // Hint: the first basic (tier-1) forced cell from the player's current
    // marks. `b` = UNKNOWN/BULB/NOBULB (the game's empty/bulb/✗ map 1:1).
    // Returns { cell, state:BULB|NOBULB, reason:'clue'|'sight'|'cover' } or null.
    // -----------------------------------------------------------------
    // Returns a *group* of cells forced by one source, so the hint can present
    // them together: { cells:[...], state:BULB|NOBULB, reason, anchor } where
    // anchor is the source wall/bulb index (-1 for coverage). null if nothing.
    function nextStep(ctx, clue, b) {
        const { N, wall, rays, wallNeigh, whites } = ctx;
        // The caller virtually ✗'es every cell already in a guard's sight, so we
        // never surface "already-watched" shadow cells. We therefore surface
        // productive GUARD placements first, then genuine (non-shadow) exclusions.

        // Pass 1a — a numbered pillar whose remaining open neighbours must all be guards.
        for (let i = 0; i < N * N; i++) {
            if (!wall[i] || clue[i] < 0) continue;
            let nb = 0, nu = 0; const unknowns = [];
            for (const j of wallNeigh[i]) { if (b[j] === BULB) nb++; else if (b[j] === UNKNOWN) { nu++; unknowns.push(j); } }
            if (nu > 0 && nb + nu === clue[i]) return { cells: unknowns, state: BULB, reason: 'clue', anchor: i };
        }
        // Pass 1b — a still-dark cell with a single possible watcher → place it there.
        const lit = new Uint8Array(N * N);
        for (const i of whites) if (b[i] === BULB) { lit[i] = 1; for (const j of rays[i]) lit[j] = 1; }
        for (const i of whites) {
            if (lit[i]) continue;
            let only = -1, cnt = 0;
            if (b[i] !== NOBULB) { only = i; cnt++; }
            for (const j of rays[i]) { if (b[j] !== NOBULB) { only = j; cnt++; if (cnt > 1) break; } }
            if (cnt === 1 && b[only] === UNKNOWN) return { cells: [only], state: BULB, reason: 'cover', anchor: i };
        }
        // Pass 2 — a genuine exclusion: a satisfied pillar forbids guards on the rest.
        for (let i = 0; i < N * N; i++) {
            if (!wall[i] || clue[i] < 0) continue;
            let nb = 0; const unknowns = [];
            for (const j of wallNeigh[i]) { if (b[j] === BULB) nb++; else if (b[j] === UNKNOWN) unknowns.push(j); }
            if (unknowns.length && nb === clue[i]) return { cells: unknowns, state: NOBULB, reason: 'clue', anchor: i };
        }
        return null;
    }

    // -----------------------------------------------------------------
    // Deep hint (Tier-2 UI): when pure propagation stalls, find a cell whose one
    // value refutes itself, and return the minimal "assume → contradiction" chain
    // so the UI can draw each forced step and point at the broken rule. This is
    // the Guards analogue of Tango's L2 hint.
    // -----------------------------------------------------------------

    // Propagation that records, for every cell it forces, the cells that justified
    // it (`src`), and on a contradiction the broken rule + the cells involved.
    // Mutates `b`. Used only by the hint (rare), so clarity over micro-speed.
    function propagateTraced(ctx, clue, b) {
        const { N, wall, rays, wallNeigh, whites } = ctx;
        const trace = [];
        const set = (j, val, src) => { b[j] = val; trace.push({ cell: j, val, src }); };
        let changed = true;
        while (changed) {
            changed = false;
            for (let i = 0; i < N * N; i++) {
                if (!wall[i] || clue[i] < 0) continue;
                const ns = wallNeigh[i];
                let nb = 0, nu = 0; const bulbs = [], nobulbs = [], unknowns = [];
                for (const j of ns) { if (b[j] === BULB) { nb++; bulbs.push(j); } else if (b[j] === UNKNOWN) { nu++; unknowns.push(j); } else nobulbs.push(j); }
                // The forced guards / ✗s around the pillar become numbered chain
                // steps (seed), and ONLY the pillar is the red "where it breaks"
                // locus (cells empty here; repaint rings bad.pillar).
                if (nb > clue[i]) return { ok: false, trace, bad: { kind: 'clue', pillar: i, cells: [], seed: bulbs.slice() } };
                if (nb + nu < clue[i]) return { ok: false, trace, bad: { kind: 'clue', pillar: i, cells: [], seed: nobulbs.slice() } };
                if (nb === clue[i] && nu > 0) { for (const j of unknowns) set(j, NOBULB, bulbs.slice()); changed = true; }
                else if (nb + nu === clue[i] && nu > 0) { for (const j of unknowns) set(j, BULB, nobulbs.slice()); changed = true; }
            }
            for (const i of whites) {
                if (b[i] !== BULB) continue;
                for (const j of rays[i]) {
                    if (b[j] === BULB) return { ok: false, trace, bad: { kind: 'sight', cells: [i, j], seed: [i, j] } };
                    if (b[j] === UNKNOWN) { set(j, NOBULB, [i]); changed = true; }
                }
            }
            const lit = new Uint8Array(N * N);
            for (const i of whites) if (b[i] === BULB) { lit[i] = 1; for (const j of rays[i]) lit[j] = 1; }
            for (const i of whites) {
                if (lit[i]) continue;
                let only = -1, cnt = 0; const ruled = [];
                if (b[i] !== NOBULB) { only = i; cnt++; } else ruled.push(i);
                for (const j of rays[i]) { if (b[j] !== NOBULB) { only = j; cnt++; } else ruled.push(j); }
                if (cnt === 0) return { ok: false, trace, bad: { kind: 'cover', cells: [i], seed: [i].concat(rays[i]) } };
                if (cnt === 1 && b[only] === UNKNOWN) { set(only, BULB, ruled.length ? ruled : [i]); changed = true; }
            }
        }
        return { ok: true, trace, bad: null };
    }

    // Smallest subset of forced steps that justify the contradiction, in order.
    function backwardClose(trace, bad) {
        const stepByCell = new Map();
        for (const s of trace) stepByCell.set(s.cell, s);
        const needed = new Set(), q = (bad.seed || bad.cells).slice();
        while (q.length) {
            const c = q.shift();
            if (needed.has(c)) continue;
            needed.add(c);
            const step = stepByCell.get(c);
            if (step) for (const s of step.src) if (!needed.has(s)) q.push(s);
        }
        const badSet = new Set(bad.cells);
        const chain = [];
        for (const s of trace) if (needed.has(s.cell) && !badSet.has(s.cell)) chain.push({ cell: s.cell, val: s.val });
        return chain;
    }

    // The shortest-chain depth-1 deduction from the current marks `b`, or null.
    // Returns { cell, state, hyp:{cell,val}, chain:[{cell,val}], bad:{kind,pillar?,cells} }.
    function nextStepDeep(ctx, clue, b) {
        let best = null;
        for (const X of ctx.whites) {
            if (b[X] !== UNKNOWN) continue;
            for (const V of [BULB, NOBULB]) {
                const t = b.slice(); t[X] = V;
                const res = propagateTraced(ctx, clue, t);
                if (!res.ok) {
                    // The simplest deduction is the shortest refutation chain (an
                    // immediate contradiction is simpler than a multi-step one).
                    const chain = backwardClose(res.trace, res.bad);
                    if (!best || chain.length < best.chain.length) {
                        best = { cell: X, state: V === BULB ? NOBULB : BULB, hyp: { cell: X, val: V }, chain, bad: res.bad };
                    }
                    break; // X=V refutes itself ⇒ X is the opposite; skip V's twin
                }
            }
        }
        return best;
    }

    // Longest minimal refutation chain the shortest-chain depth-1 solver must use
    // to finish `clue` from empty (0 if pure propagation alone solves it). Lets
    // Hard reject the occasional board with a brutally long assume→contradiction
    // chain, so every Hard hint stays followable.
    function maxTrialChain(ctx, clue) {
        const b = new Int8Array(ctx.N * ctx.N);
        let maxLen = 0, guard = 0;
        for (;;) {
            if (++guard > ctx.N * ctx.N * 4) return Infinity;
            if (!propagate(ctx, clue, b).ok) return Infinity;
            let unknown = false;
            for (const i of ctx.whites) if (b[i] === UNKNOWN) { unknown = true; break; }
            if (!unknown) return maxLen;
            const d = nextStepDeep(ctx, clue, b);
            if (!d) return Infinity;
            if (d.chain.length > maxLen) maxLen = d.chain.length;
            b[d.cell] = d.state;
        }
    }

    // -----------------------------------------------------------------
    // Generation
    // -----------------------------------------------------------------
    function randomLayout(N, rng, boost) {
        // Structured walls: grow short straight runs instead of scattering single
        // cells. Clustered/linear walls carve the grid into corridors, which makes
        // a pure-propagation (⇒ unique) solution far more likely than fully-random
        // placement — so we can run sparser and still fill the pool fast. `boost`
        // raises the target density if a size is proving hard to fill.
        let dens = 0.22 + (rng() * 0.04 - 0.02) + (boost || 0);
        dens = Math.max(0.16, Math.min(0.5, dens));
        const target = Math.round(N * N * dens);
        const wall = new Uint8Array(N * N);
        let placed = 0, guard = 0;
        while (placed < target && guard++ < N * N * 8) {
            let r = (rng() * N) | 0, c = (rng() * N) | 0;
            if (wall[r * N + c]) continue;
            const len = 1 + ((rng() * 3) | 0);              // run of 1–3 cells
            const [dr, dc] = DIRS[(rng() * DIRS.length) | 0];
            for (let s = 0; s < len && placed < target; s++) {
                if (r < 0 || r >= N || c < 0 || c >= N) break;
                const i = r * N + c;
                if (!wall[i]) { wall[i] = 1; placed++; }
                r += dr; c += dc;
            }
        }
        return wall;
    }

    // Full solve at a given trial depth (0 = pure propagation). Fully solving a
    // board ⟹ UNIQUE. Depth 0 is cheap; depth 1 adds one "assume a cell →
    // contradiction → force the opposite" layer (what Hard leans on) and is
    // pricier, so generation uses it only for Hard and only after a cheap depth-0
    // minimisation pass.
    function solvesBy(ctx, clue, depth) {
        if (depth <= 0) {
            const b = new Int8Array(ctx.N * ctx.N);
            return propagate(ctx, clue, b).ok && fullyAssigned(ctx, b) && verify(ctx, clue, b);
        }
        return solvesDepth1(ctx, clue);
    }

    // Fast depth-1 full solve (reuses a scratch trial buffer). "Assume a cell →
    // propagate → on contradiction force the opposite", iterated to a fixpoint;
    // fully solving ⟹ UNIQUE. Used as the Hard gate (pricey, so kept lean).
    function solvesDepth1(ctx, clue) {
        const b = new Int8Array(ctx.N * ctx.N);
        if (!propagate(ctx, clue, b).ok) return false;
        const t = ctx._trial;
        let changed = true;
        while (changed) {
            changed = false;
            for (const i of ctx.whites) {
                if (b[i] !== UNKNOWN) continue;
                t.set(b); t[i] = BULB;
                if (!propagate(ctx, clue, t).ok) {
                    b[i] = NOBULB;
                    if (!propagate(ctx, clue, b).ok) return false;
                    changed = true; continue;
                }
                t.set(b); t[i] = NOBULB;
                if (!propagate(ctx, clue, t).ok) {
                    b[i] = BULB;
                    if (!propagate(ctx, clue, b).ok) return false;
                    changed = true; continue;
                }
            }
        }
        return fullyAssigned(ctx, b) && verify(ctx, clue, b);
    }

    // A random valid bulb solution (no two see each other, all white lit).
    // Always succeeds: lighting an unlit cell from itself is conflict-free.
    function buildSolution(ctx, rng) {
        const { N, rays, whites } = ctx;
        const b = new Int8Array(N * N);
        const lit = new Uint8Array(N * N);
        const relight = (i) => { lit[i] = 1; for (const j of rays[i]) lit[j] = 1; };
        const seesBulb = (p) => { for (const j of rays[p]) if (b[j] === BULB) return true; return false; };
        let guard = 0;
        for (;;) {
            if (++guard > N * N * 4) return null;
            let unlit = null;
            // random scan for an unlit white cell
            const start = (rng() * whites.length) | 0;
            for (let k = 0; k < whites.length; k++) {
                const i = whites[(start + k) % whites.length];
                if (!lit[i]) { unlit = i; break; }
            }
            if (unlit == null) break; // all lit
            const cands = [];
            if (!seesBulb(unlit)) cands.push(unlit);
            for (const j of rays[unlit]) if (b[j] !== BULB && !seesBulb(j)) cands.push(j);
            if (!cands.length) return null; // shouldn't happen (unlit ⇒ self is conflict-free)
            const p = cands[(rng() * cands.length) | 0];
            b[p] = BULB; relight(p);
        }
        return b;
    }

    function deriveClues(ctx, sol) {
        const { N, wall, wallNeigh } = ctx;
        const clue = new Int8Array(N * N).fill(-1);
        for (let i = 0; i < N * N; i++) {
            if (!wall[i]) continue;
            let cnt = 0;
            for (const j of wallNeigh[i]) if (sol[j] === BULB) cnt++;
            clue[i] = cnt;
        }
        return clue;
    }

    function attemptsFor(N) { return N <= 10 ? 200 : N <= 13 ? 150 : 120; }

    // One candidate from a wall layout, or null if the fully-numbered board isn't
    // solvable at this difficulty's depth. Then strips 0-clues and numbered clues
    // at per-difficulty rates while the board stays solvable — fewer clues ⟹
    // harder. For Hard, after the cheap depth-0 strip it keeps stripping while a
    // depth-1 solve still works, pushing the board to genuinely need the
    // "assume → contradiction" step. Mutates nothing shared.
    function buildCandidate(N, wall, rng, cfg) {
        const ctx = makeCtx(N, wall);
        if (ctx.whites.length < 4) return null;
        const sol = buildSolution(ctx, rng);
        if (!sol) return null;
        const full = deriveClues(ctx, sol);
        if (!solvesBy(ctx, full, cfg.gateDepth)) return null; // ambiguous even fully numbered
        const clue = full.slice();
        const zeros = [], nums = [];
        for (let i = 0; i < N * N; i++) if (clue[i] >= 0) (clue[i] === 0 ? zeros : nums).push(i);
        PC.rng.shuffle(zeros, rng); PC.rng.shuffle(nums, rng);
        // Phase 1 — cheap depth-0 strip at the per-difficulty rates.
        const strip = (list, frac) => {
            const k = Math.round(list.length * Math.max(0, Math.min(1, frac)));
            for (let t = 0; t < k; t++) {
                const w = list[t];
                const saved = clue[w]; clue[w] = -1;
                if (!solvesBy(ctx, clue, 0)) clue[w] = saved;
            }
        };
        strip(zeros, cfg.zeroFrac);
        strip(nums, cfg.numFrac);
        // Phase 2 (Hard) — after the depth-0 minimisation the board is still
        // pure-propagation solvable; strip a little further while a depth-1 solve
        // holds, so it genuinely needs the trial step. Stop a few strips after it
        // crosses into tier-1 (depth-1 checks are pricey — this keeps even N=25
        // fast) while still deepening past the bare minimum.
        if (cfg.gateDepth >= 1) {
            const rest = [];
            for (let i = 0; i < N * N; i++) if (clue[i] >= 0) rest.push(i);
            PC.rng.shuffle(rest, rng);
            for (const w of rest) {
                const saved = clue[w]; clue[w] = -1;
                if (!solvesBy(ctx, clue, 1)) clue[w] = saved;
            }
        }
        const tier = solvesBy(ctx, clue, 0) ? 0 : 1;
        const maxChain = (tier === 1 && cfg.gateDepth >= 1) ? maxTrialChain(ctx, clue) : 0;
        const passes = propagate(ctx, clue, new Int8Array(N * N)).passes;
        let shown = 0, total = 0, zerosShown = 0;
        for (let i = 0; i < N * N; i++) if (wall[i]) { total++; if (clue[i] >= 0) { shown++; if (clue[i] === 0) zerosShown++; } }
        return { wall, clue, sol, shown, total, zerosShown, passes, tier, maxChain, ratio: total ? shown / total : 0 };
    }

    async function generate(size, difficulty, seed, onProgress) {
        const N = size;
        const rng = PC.rng.make(seed >>> 0);
        const softCap = attemptsFor(N);
        const hardCap = softCap * 10;
        // Minimisation aggressiveness per difficulty: Easy keeps most numbers
        // (shallow), Hard strips to a near-minimal set (deep). Fewer numbers =
        // harder, like real Akari.
        const base = DIFFS[difficulty] || DIFFS.medium;
        // Depth-1 minimisation is pricey on big boards; cap it to sizes where it
        // stays snappy (≤20, under ~1.5s). Beyond that, Hard falls back to the
        // sparsest no-guess board so the largest size never stalls.
        const cfg = (difficulty === 'hard' && N > 20) ? { ...base, gateDepth: 0 } : base;
        if (onProgress) await onProgress(0.03);

        // Collect a pool. Easy/Medium stop once there's a board past the soft cap.
        // Hard stops as soon as it finds a board that genuinely needs the depth-1
        // trial (tier 1) — those are what make it hard. Never empty → no blank.
        const pool = [];
        for (let t = 0; t < hardCap; t++) {
            const boost = Math.floor(t / softCap) * 0.05;
            const cand = buildCandidate(N, randomLayout(N, rng, boost), rng, cfg);
            if (cand) pool.push(cand);
            if (difficulty === 'hard' && cfg.gateDepth >= 1) { if (cand && cand.tier === 1 && cand.maxChain <= cfg.maxChain) break; }
            else if (t >= softCap && pool.length >= 1) break;
            if (onProgress && (t & 7) === 0) await onProgress(0.03 + 0.9 * Math.min(1, (t + 1) / softCap));
        }

        if (onProgress) await onProgress(0.97);
        if (!pool.length) {
            // Effectively unreachable, but never ship a blank board.
            for (let tries = 0; tries < 500 && !pool.length; tries++) {
                const cand = buildCandidate(N, randomLayout(N, rng, 0.18), rng, cfg);
                if (cand) pool.push(cand);
            }
        }

        // Pick a representative. Hard: the deepest board that needs the depth-1
        // trial (fall back to deepest overall if—rarely—none did). Easy/Medium: a
        // chain-depth percentile (easy = shallower end).
        let chosen;
        if (difficulty === 'hard') {
            const deep = pool.filter((c) => c.tier === 1 && c.maxChain <= cfg.maxChain);
            const use = (deep.length ? deep : pool).sort((a, b) => a.passes - b.passes);
            chosen = use[use.length - 1];
        } else {
            pool.sort((a, b) => a.passes - b.passes);
            const pct = difficulty === 'easy' ? 0.3 : 0.5;
            chosen = pool[Math.round((pool.length - 1) * pct)];
        }

        // Output grid: -2 white, -1 wall (no number), 0..4 wall (number).
        const grid = [];
        for (let r = 0; r < N; r++) {
            const row = [];
            for (let c = 0; c < N; c++) {
                const i = r * N + c;
                row.push(chosen.wall[i] ? (chosen.clue[i] >= 0 ? chosen.clue[i] : -1) : -2);
            }
            grid.push(row);
        }
        const solution = [];
        for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (chosen.sol[r * N + c] === BULB) solution.push([r, c]);

        if (onProgress) await onProgress(1);
        return {
            id: `guards-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'guards', size: N, difficulty,
            grid, solution,
            stats: { score: chosen.passes, passes: chosen.passes, shown: chosen.shown, total: chosen.total, ratio: chosen.ratio, tier: chosen.tier, poolSize: pool.length },
        };
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleGenerators.guards = generate;
    global.PuzzleSolvers.guards = { makeCtx, propagate, solveTier, countSolutions, verify, nextStep, nextStepDeep };
    global.PuzzleGenerators.guardsInternals = {
        makeCtx, propagate, deductiveSolve, solveTier, solvesBy, solvesDepth1, countSolutions, verify,
        nextStep, nextStepDeep, buildSolution, deriveClues, randomLayout, attemptsFor, UNKNOWN, BULB, NOBULB,
    };
})(typeof window !== 'undefined' ? window : this);
