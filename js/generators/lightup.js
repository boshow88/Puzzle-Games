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
 *   window.PuzzleGenerators.lightup(size, difficulty, seed, onProgress)
 *     → { id, game:'lightup', size, difficulty, grid, solution, stats }
 *   window.PuzzleSolvers.lightup       — { propagate, solveTier, countSolutions }
 *   window.PuzzleGenerators.lightupInternals — for the self-test
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    // Solver bulb-state for white cells.
    const UNKNOWN = 0, BULB = 1, NOBULB = 2;
    const MAX_TRIAL = 2; // deepest "assume & check" nesting we accept (keeps it fair)

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
        return { N, wall, rays, wallNeigh, whites };
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
            const lit = new Uint8Array(N * N);
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
    function nextStep(ctx, clue, b) {
        const { N, wall, rays, wallNeigh, whites } = ctx;
        for (let i = 0; i < N * N; i++) {
            if (!wall[i] || clue[i] < 0) continue;
            const ns = wallNeigh[i];
            let nb = 0, nu = 0, firstU = -1;
            for (const j of ns) { if (b[j] === BULB) nb++; else if (b[j] === UNKNOWN) { nu++; if (firstU < 0) firstU = j; } }
            if (nu > 0 && nb === clue[i]) return { cell: firstU, state: NOBULB, reason: 'clue', wall: i };
            if (nu > 0 && nb + nu === clue[i]) return { cell: firstU, state: BULB, reason: 'clue', wall: i };
        }
        for (const i of whites) {
            if (b[i] !== BULB) continue;
            for (const j of rays[i]) if (b[j] === UNKNOWN) return { cell: j, state: NOBULB, reason: 'sight', from: i };
        }
        const lit = new Uint8Array(N * N);
        for (const i of whites) if (b[i] === BULB) { lit[i] = 1; for (const j of rays[i]) lit[j] = 1; }
        for (const i of whites) {
            if (lit[i]) continue;
            let only = -1, cnt = 0;
            if (b[i] !== NOBULB) { only = i; cnt++; }
            for (const j of rays[i]) { if (b[j] !== NOBULB) { only = j; cnt++; if (cnt > 1) break; } }
            if (cnt === 1 && b[only] === UNKNOWN) return { cell: only, state: BULB, reason: 'cover' };
        }
        return null;
    }

    // -----------------------------------------------------------------
    // Generation
    // -----------------------------------------------------------------
    function randomLayout(N, rng) {
        const p = 0.16 + 0.10 * rng(); // wall density ~0.16–0.26
        const wall = new Uint8Array(N * N);
        for (let i = 0; i < N * N; i++) if (rng() < p) wall[i] = 1;
        return wall;
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

    function attemptsFor(N) { return N <= 9 ? 90 : N <= 12 ? 60 : 36; }

    async function generate(size, difficulty, seed, onProgress) {
        const N = size;
        const rng = PC.rng.make(seed >>> 0);
        const attempts = attemptsFor(N);
        if (onProgress) await onProgress(0.03);

        const pool = [];
        for (let t = 0; t < attempts; t++) {
            const wall = randomLayout(N, rng);
            const ctx = makeCtx(N, wall);
            if (ctx.whites.length < 4) continue;
            const sol = buildSolution(ctx, rng);
            if (!sol) continue;
            const full = deriveClues(ctx, sol);
            // Must be uniquely solvable with every number shown, else discard.
            if (countSolutions(ctx, full, 2) !== 1) continue;

            // Random reveal ratio: drop a random share of numbers while the
            // puzzle stays uniquely solvable, so the shown-number ratio varies
            // as a *style* rather than being the difficulty itself.
            const clue = full.slice();
            const wallsWithNum = [];
            for (let i = 0; i < N * N; i++) if (clue[i] >= 0) wallsWithNum.push(i);
            PC.rng.shuffle(wallsWithNum, rng);
            const dropP = 0.25 + 0.65 * rng();
            for (const w of wallsWithNum) {
                if (rng() >= dropP) continue;
                const saved = clue[w]; clue[w] = -1;
                if (countSolutions(ctx, clue, 2) !== 1) clue[w] = saved;
            }

            const st = solveTier(ctx, clue);
            if (!st.solved) continue; // needs deeper than MAX_TRIAL → too guessy, skip
            const shown = wallsWithNum.filter((i) => clue[i] >= 0).length;
            const ratio = wallsWithNum.length ? shown / wallsWithNum.length : 0;
            pool.push({ wall, clue, sol, score: st.tier * 1000 + st.passes, tier: st.tier, passes: st.passes, ratio });

            if (onProgress && (t & 7) === 0) await onProgress(0.03 + 0.92 * (t + 1) / attempts);
        }

        if (onProgress) await onProgress(0.97);
        if (!pool.length) {
            // Degenerate fallback: a tiny all-revealed board (should ~never hit).
            const wall = new Uint8Array(N * N); const ctx = makeCtx(N, wall);
            const sol = buildSolution(ctx, rng) || new Int8Array(N * N);
            const clue = deriveClues(ctx, sol);
            pool.push({ wall, clue, sol, score: 0, tier: 0, passes: 1, ratio: 1 });
        }

        pool.sort((a, b) => a.score - b.score);
        const idx = difficulty === 'easy' ? 0
            : difficulty === 'hard' ? pool.length - 1
                : Math.floor((pool.length - 1) * 0.5);
        const chosen = pool[idx];

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
            id: `lightup-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'lightup', size: N, difficulty,
            grid, solution,
            stats: { score: chosen.score, tier: chosen.tier, passes: chosen.passes, ratio: chosen.ratio, poolSize: pool.length },
        };
    }

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleGenerators.lightup = generate;
    global.PuzzleSolvers.lightup = { makeCtx, propagate, solveTier, countSolutions, verify, nextStep };
    global.PuzzleGenerators.lightupInternals = {
        makeCtx, propagate, deductiveSolve, solveTier, countSolutions, verify,
        buildSolution, deriveClues, randomLayout, attemptsFor, UNKNOWN, BULB, NOBULB,
    };
})(typeof window !== 'undefined' ? window : this);
