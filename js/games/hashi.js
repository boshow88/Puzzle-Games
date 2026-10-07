/**
 * Hashi (Bridges / Hashiwokakero) — game UI.
 *
 * Consumes window.PuzzleGenerators.hashi + the shared shell. Input is a drag
 * from an island toward an orthogonally-adjacent island: each drag cycles that
 * connection 0 → 1 → 2 → 0 bridges. Win when every island's bridge count equals
 * its number, no two bridges cross, and all islands form one connected network.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;
    const HS = window.PuzzleSolvers.hashi;
    const BOARD = 480;
    const VIOLATION_DELAY_MS = 800;
    // Add ?hashi_debug=1 to the URL to log each hint's full reasoning + a board
    // snapshot to the console (handy for reporting a confusing hint).
    const DEBUG = typeof location !== 'undefined' && /[?&]hashi_debug=1\b/.test(location.search);

    const SIZE_STEPS = [7, 9, 11, 13, 15, 17, 21, 25];
    const MIN_SIZE = 7, MAX_SIZE = 25;
    const VALID_DIFFS = new Set(['easy', 'medium', 'hard']);

    function readUrlInitial() {
        if (!PC.share) return null;
        const raw = PC.share.readParams();
        if (!(raw.size >= MIN_SIZE && raw.size <= MAX_SIZE)) return null;
        if (!VALID_DIFFS.has(raw.difficulty)) return null;
        if (!Number.isInteger(raw.seed)) return null;
        return { size: raw.size, difficulty: raw.difficulty, seed: raw.seed };
    }
    const urlInitial = readUrlInitial();
    let pendingSeed = urlInitial ? urlInitial.seed : null;

    async function onShareClick() {
        if (!PC.share) return;
        const ok = await PC.share.copyCurrentUrl();
        if (PC.toast) PC.toast.show(PC.i18n.t(ok ? 'shareCopied' : 'shareFailed'));
    }

    // -----------------------------------------------------------------
    // State
    // -----------------------------------------------------------------
    const state = {
        puzzle: null,
        N: 0,
        islands: null,          // [{r,c,need}]
        G: null,                // buildGraph result
        needs: null,            // Int16Array of island numbers
        solVal: null,           // Int8Array solution bridge count per edge
        edgeVal: null,          // Int8Array player bridge count per edge (0..2)
        edgeMark: null,         // Int8Array per-edge "count confirmed" annotation (0/1)
        doneMark: null,         // Int8Array per-island "handled" annotation
        dirEdge: null,          // per island: {U,D,L,R} → edge index
        mode: 'build',          // 'build' (lay bridges) | 'mark' (annotate confirmed)
        hoverEdge: -1,          // corridor under the mouse (hover preview)
        hoverIsland: -1,        // island under the mouse (mark-mode hover preview)
        lastEdge: -1,           // most recently edited edge (win animation radiates from it)
        won: false,
        hint: null, hintBanner: null,
        dragging: null,         // { pointerId, from, pending }
        displayed: { over: [], cross: [] }, // shown conflicts (option B)
        violationTimer: null,
        cs: 0,
    };
    let shell = null, board = null, undoHistory = null;

    async function generatePuzzle(size, difficulty, seed) {
        return window.PuzzleGenerators.hashi(size, difficulty, seed, null);
    }

    function parsePuzzle(p) {
        const N = p.size;
        state.N = N;
        state.islands = p.islands.map((is) => ({ r: is.r, c: is.c, need: is.need }));
        state.G = HS.buildGraph(N, state.islands);
        state.needs = state.islands.map((is) => is.need);
        const E = state.G.edges.length;
        state.solVal = new Int8Array(E);
        for (const br of p.solution) {
            const e = state.G.edges.findIndex((ed) => (ed.a === br.a && ed.b === br.b) || (ed.a === br.b && ed.b === br.a));
            if (e >= 0) state.solVal[e] = br.v;
        }
        state.edgeVal = new Int8Array(E);
        state.edgeMark = new Int8Array(E);                    // player's "count confirmed" flags
        state.doneMark = new Int8Array(state.islands.length); // player's "handled" flags
        // Per-island direction → edge map for drag resolution.
        state.dirEdge = state.islands.map(() => ({}));
        for (let e = 0; e < E; e++) {
            const { a, b } = state.G.edges[e];
            const A = state.islands[a], B = state.islands[b];
            if (A.r === B.r) {
                if (B.c > A.c) { state.dirEdge[a].R = e; state.dirEdge[b].L = e; }
                else { state.dirEdge[a].L = e; state.dirEdge[b].R = e; }
            } else {
                if (B.r > A.r) { state.dirEdge[a].D = e; state.dirEdge[b].U = e; }
                else { state.dirEdge[a].U = e; state.dirEdge[b].D = e; }
            }
        }
    }

    // -----------------------------------------------------------------
    // Rule helpers
    // -----------------------------------------------------------------
    function islandSum(v) { let s = 0; for (const e of state.G.incident[v]) s += state.edgeVal[e]; return s; }

    function rulesSatisfied() {
        const { G, needs, edgeVal } = state;
        for (let v = 0; v < G.islands.length; v++) if (islandSum(v) !== needs[v]) return false;
        for (let e = 0; e < G.edges.length; e++) if (edgeVal[e] >= 1) for (const f of G.cross[e]) if (edgeVal[f] >= 1) return false;
        // connectivity
        const m = G.islands.length;
        const parent = new Int32Array(m); for (let i = 0; i < m; i++) parent[i] = i;
        const find = (x) => { while (parent[x] !== x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; };
        for (let e = 0; e < G.edges.length; e++) if (edgeVal[e] >= 1) { const a = find(G.edges[e].a), b = find(G.edges[e].b); if (a !== b) parent[a] = b; }
        const r0 = find(0);
        for (let i = 1; i < m; i++) if (find(i) !== r0) return false;
        return true;
    }

    // -----------------------------------------------------------------
    // Conflict display — option B (mirror of Guards)
    // -----------------------------------------------------------------
    function computeViolations() {
        const { G, needs, edgeVal } = state;
        const over = [];
        for (let v = 0; v < G.islands.length; v++) if (islandSum(v) > needs[v]) over.push(v);
        const cross = [];
        for (let e = 0; e < G.edges.length; e++) if (edgeVal[e] >= 1) for (const f of G.cross[e]) if (f > e && edgeVal[f] >= 1) cross.push([e, f]);
        return { over, cross };
    }
    const pairKey = (i, j) => i + '-' + j;
    function cancelViolationTimer() { if (state.violationTimer) { clearTimeout(state.violationTimer); state.violationTimer = null; } }
    function violationCount() { return state.displayed.over.length + state.displayed.cross.length; }
    function updateViolationPill() { if (shell && shell.setViolationCount) shell.setViolationCount(violationCount()); }
    function setDisplayedFull(v) { state.displayed = { over: v.over.slice(), cross: v.cross.slice() }; }
    function commitViolations() { state.violationTimer = null; setDisplayedFull(computeViolations()); repaint(); updateStatusRow(); }
    function refreshViolationsOnEdit() {
        const t = computeViolations();
        const overSet = new Set(t.over);
        const crossSet = new Set(t.cross.map(([i, j]) => pairKey(i, j)));
        state.displayed.over = state.displayed.over.filter((v) => overSet.has(v));
        state.displayed.cross = state.displayed.cross.filter(([i, j]) => crossSet.has(pairKey(i, j)));
        cancelViolationTimer();
        state.violationTimer = setTimeout(commitViolations, VIOLATION_DELAY_MS);
    }
    function showAllViolationsNow() { cancelViolationTimer(); setDisplayedFull(computeViolations()); }
    function clearViolations() { cancelViolationTimer(); state.displayed = { over: [], cross: [] }; }

    // -----------------------------------------------------------------
    // Render
    // -----------------------------------------------------------------
    function computeLayout() { state.cs = BOARD / state.N; }
    function cx(c) { return c * state.cs + state.cs / 2; }
    function cy(r) { return r * state.cs + state.cs / 2; }

    function renderBoard() {
        computeLayout();
        // Island ring thickness scales with cell size (capped at 2.5 for small
        // boards), so big boards like 25×25 don't get chunky rings. State variants
        // (e.g. .active) multiply this via calc().
        board.style.setProperty('--hashi-isle-sw', Math.max(1.1, Math.min(2.5, state.cs * 0.08)).toFixed(2) + 'px');
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);
        svg.appendChild(PC.svgEl('rect', { class: 'hashi-bg', x: 0, y: 0, width: BOARD, height: BOARD }));
        // Faint lattice through the island centres, so islands read as sitting on
        // grid intersections and the row/column relationships are easy to see.
        const grid = PC.svgEl('g', { class: 'hashi-grid' });
        const lo = cx(0), hi = cx(state.N - 1);
        for (let i = 0; i < state.N; i++) {
            const p = i * state.cs + state.cs / 2;
            grid.appendChild(PC.svgEl('line', { class: 'hashi-grid-line', x1: p, y1: lo, x2: p, y2: hi }));
            grid.appendChild(PC.svgEl('line', { class: 'hashi-grid-line', x1: lo, y1: p, x2: hi, y2: p }));
        }
        svg.appendChild(grid);
        const bridges = PC.svgEl('g'); bridges.setAttribute('id', 'hashi-bridges'); svg.appendChild(bridges);
        const hint = PC.svgEl('g'); hint.setAttribute('id', 'hashi-hint'); svg.appendChild(hint);
        const reveal = PC.svgEl('g'); reveal.setAttribute('id', 'hashi-reveal'); svg.appendChild(reveal);
        const isl = PC.svgEl('g'); isl.setAttribute('id', 'hashi-islands'); svg.appendChild(isl);
        repaint();
    }

    function bridgeLine(cls, r1, c1, r2, c2, off, sw) {
        // off = perpendicular offset for the two lines of a double bridge
        let dx = 0, dy = 0;
        if (r1 === r2) dy = off; else dx = off;
        return PC.svgEl('line', {
            class: cls, 'stroke-width': sw,
            x1: cx(c1) + dx, y1: cy(r1) + dy, x2: cx(c2) + dx, y2: cy(r2) + dy,
        });
    }

    function drawBridge(layer, e, val, cls, sw, offUnit, delay) {
        const { a, b } = state.G.edges[e];
        const A = state.islands[a], B = state.islands[b];
        const add = (ln) => { if (delay) ln.style.animationDelay = delay; layer.appendChild(ln); };
        if (val === 1) {
            add(bridgeLine(cls, A.r, A.c, B.r, B.c, 0, sw));
        } else if (val === 2) {
            add(bridgeLine(cls, A.r, A.c, B.r, B.c, -offUnit, sw));
            add(bridgeLine(cls, A.r, A.c, B.r, B.c, offUnit, sw));
        }
    }
    // A faint dotted segment down the middle of a corridor confirmed to be empty.
    // (A confirmed bridge instead recolours grey — see the bridges loop.)
    function drawEmptyMark(layer, e, preview, fadeDelay) {
        const { a, b } = state.G.edges[e], A = state.islands[a], B = state.islands[b];
        const ax = cx(A.c), ay = cy(A.r), bx = cx(B.c), by = cy(B.r);
        const ln = PC.svgEl('line', {
            class: 'hashi-mark-empty' + (preview ? ' preview' : '') + (fadeDelay ? ' won-fade' : ''), 'stroke-width': Math.max(2, state.cs * 0.05),
            x1: ax + (bx - ax) * 0.3, y1: ay + (by - ay) * 0.3, x2: ax + (bx - ax) * 0.7, y2: ay + (by - ay) * 0.7,
        });
        if (fadeDelay) ln.style.animationDelay = fadeDelay;
        layer.appendChild(ln);
    }

    function repaint() {
        const { G, cs, won } = state;
        const bl = board.querySelector('#hashi-bridges');
        const il = board.querySelector('#hashi-islands');
        if (!bl || !il) return;
        while (bl.firstChild) bl.removeChild(bl.firstChild);
        while (il.firstChild) il.removeChild(il.firstChild);

        const overSet = new Set(state.displayed.over);
        const crossSet = new Set();
        for (const [i, j] of state.displayed.cross) { crossSet.add(i); crossSet.add(j); }

        const sw = Math.max(2, cs * 0.07);
        const offUnit = Math.max(2.2, cs * 0.1);
        // On win the green colour + pop flow THROUGH the bridge network from the
        // last-placed bridge — a breadth-first spread by hop count along the drawn
        // bridges (so it travels along the connections, not as a straight-line ripple).
        let winLevel = null, winMaxL = 0;
        if (won && state.lastEdge >= 0 && state.lastEdge < G.edges.length) {
            const m = G.islands.length;
            winLevel = new Int32Array(m).fill(-1);
            const le = G.edges[state.lastEdge], q = [le.a, le.b];
            winLevel[le.a] = 0; winLevel[le.b] = 0;
            for (let h = 0; h < q.length; h++) {
                const u = q[h];
                for (const e of G.incident[u]) {
                    if (state.edgeVal[e] < 1) continue; // travel only along actual bridges
                    const w = G.edges[e].a === u ? G.edges[e].b : G.edges[e].a;
                    if (winLevel[w] === -1) { winLevel[w] = winLevel[u] + 1; q.push(w); }
                }
            }
            for (let v = 0; v < m; v++) if (winLevel[v] > winMaxL) winMaxL = winLevel[v];
        }
        const SPREAD = 0.8;
        const islandDelay = (v) => {
            if (!winLevel) return undefined;
            if (winMaxL <= 0 || winLevel[v] < 0) return '0s';
            return (winLevel[v] / winMaxL * SPREAD).toFixed(3) + 's';
        };
        const edgeDelay = (e) => {
            if (!winLevel) return undefined;
            if (winMaxL <= 0) return '0s';
            const { a, b } = G.edges[e];
            const la = winLevel[a] >= 0 ? winLevel[a] : winLevel[b];
            const lb = winLevel[b] >= 0 ? winLevel[b] : winLevel[a];
            if (la < 0 && lb < 0) return '0s';
            return ((Math.min(la, lb) + 0.5) / winMaxL * SPREAD).toFixed(3) + 's';
        };
        // Bridges. A "confirmed" bridge (Mark mode) recolours grey — it reads as
        // settled, so attention stays on the brown, still-tentative connections.
        for (let e = 0; e < G.edges.length; e++) {
            if (state.edgeVal[e] < 1) continue;
            const bad = !won && crossSet.has(e);
            const marked = !bad && state.edgeMark[e]; // keep grey even on win, so it conducts grey→green (no snap through brown)
            const delay = won ? edgeDelay(e) : undefined;
            drawBridge(bl, e, state.edgeVal[e], 'hashi-bridge' + (bad ? ' bad' : '') + (won ? ' won' : '') + (marked ? ' marked' : ''), sw, offUnit, delay);
        }
        // A corridor confirmed empty shows a faint dotted ghost down its middle.
        // On win it fades out in step with the colour wave (rather than vanishing).
        for (let e = 0; e < G.edges.length; e++) {
            if (!(state.edgeMark[e] && state.edgeVal[e] === 0 && !crossingBlocked(e))) continue;
            if (won) drawEmptyMark(bl, e, false, edgeDelay(e));
            else drawEmptyMark(bl, e);
        }
        // Drag highlight + a preview of the bridge the release will lay down.
        const d = state.dragging;
        // Hover preview (mouse). Build: ghost the bridge a click would place. Mark:
        // a faint confirm badge on the corridor, or a ring on the island, you'd set.
        if (!d && !won) {
            if (state.mode === 'build' && state.hoverEdge >= 0) {
                const e = state.hoverEdge, cur = state.edgeVal[e], nv = (cur + 1) % 3;
                if (nv === 0) drawBridge(bl, e, Math.max(1, cur), 'hashi-pending-line erase hashi-hover', sw, offUnit);
                else drawBridge(bl, e, nv, 'hashi-pending-line hashi-hover', sw, offUnit);
            } else if (state.mode === 'mark' && state.hoverEdge >= 0 && !state.edgeMark[state.hoverEdge]) {
                const e = state.hoverEdge;
                if (state.edgeVal[e] >= 1) drawBridge(bl, e, state.edgeVal[e], 'hashi-bridge marked hashi-hover', sw, offUnit);
                else drawEmptyMark(bl, e, true);
            } else if (state.mode === 'mark' && state.hoverIsland >= 0
                && (state.doneMark[state.hoverIsland] || islandSum(state.hoverIsland) === state.needs[state.hoverIsland])) {
                const is = state.islands[state.hoverIsland]; // only full (or already-done) islands are markable
                bl.appendChild(PC.svgEl('circle', { class: 'hashi-hover-isle', cx: cx(is.c), cy: cy(is.r), r: cs * 0.42 }));
            }
        }
        const active = new Set();
        if (d && d.mode === 'island' && !won) {
            active.add(d.from);
            if (d.pending >= 0) {
                const ed = G.edges[d.pending];
                active.add(ed.a); active.add(ed.b);
                const cur = state.edgeVal[d.pending];
                const nv = d.button === 2 ? (cur + 2) % 3 : (cur + 1) % 3;
                if (nv === 0) drawBridge(bl, d.pending, Math.max(1, cur), 'hashi-pending-line erase', sw, offUnit);
                else drawBridge(bl, d.pending, nv, 'hashi-pending-line', sw, offUnit);
            }
        }
        // Islands
        const rad = cs * 0.34;
        const font = Math.max(11, Math.round(cs * 0.4));
        for (let v = 0; v < G.islands.length; v++) {
            const is = state.islands[v];
            const satisfied = islandSum(v) === state.needs[v];
            const over = !won && overSet.has(v);
            const marked = state.doneMark[v]; // keep on win so a done island conducts slate→green (no snap)
            const cls = 'hashi-island'
                + (satisfied ? ' done' : '')
                + (marked ? ' marked' : '')
                + (over ? ' bad' : '')
                + (won ? ' won' : '')
                + (active.has(v) ? ' active' : '');
            const g = PC.svgEl('g', { class: cls });
            const disc = PC.svgEl('circle', { class: 'hashi-isle-disc', cx: cx(is.c), cy: cy(is.r), r: rad });
            const t = PC.svgEl('text', {
                class: 'hashi-isle-num', x: cx(is.c), y: cy(is.r),
                'text-anchor': 'middle', 'dominant-baseline': 'middle', dy: '0.08em', 'font-size': font,
            });
            t.textContent = String(state.needs[v]);
            if (won) {
                const dly = islandDelay(v);
                if (dly) { disc.style.animationDelay = dly; t.style.animationDelay = dly; }
            }
            g.appendChild(disc);
            g.appendChild(t);
            il.appendChild(g);
        }
    }

    // -----------------------------------------------------------------
    // Interaction — drag from an island toward a neighbour
    // -----------------------------------------------------------------
    function eventToPoint(ev) {
        const rect = board.getBoundingClientRect();
        if (!rect.width || !rect.height) return null;
        const x = (ev.clientX - rect.left) / rect.width * 486 - 3;
        const y = (ev.clientY - rect.top) / rect.height * 486 - 3;
        return { x, y };
    }
    function nearestIsland(pt) {
        let best = -1, bestD = state.cs * 0.55;
        for (let v = 0; v < state.islands.length; v++) {
            const dx = pt.x - cx(state.islands[v].c), dy = pt.y - cy(state.islands[v].r);
            const d = Math.hypot(dx, dy);
            if (d < bestD) { bestD = d; best = v; }
        }
        return best;
    }
    // Which candidate bridge a free point sits on (clicking the space between two
    // islands), or -1 if the point isn't clearly inside a corridor.
    function edgeAtPoint(pt) {
        let best = -1, bestD = state.cs * 0.4;
        for (let e = 0; e < state.G.edges.length; e++) {
            if (crossingBlocked(e)) continue; // a corridor an existing bridge crosses isn't a real option
            const { a, b } = state.G.edges[e];
            const A = state.islands[a], B = state.islands[b];
            const ax = cx(A.c), ay = cy(A.r), bx = cx(B.c), by = cy(B.r);
            const vx = bx - ax, vy = by - ay, L2 = (vx * vx + vy * vy) || 1;
            const t = ((pt.x - ax) * vx + (pt.y - ay) * vy) / L2;
            if (t < 0.15 || t > 0.85) continue; // keep clear of the island ends
            const d = Math.hypot(pt.x - (ax + t * vx), pt.y - (ay + t * vy));
            if (d < bestD) { bestD = d; best = e; }
        }
        return best;
    }

    // During an island drag, the neighbour edge once the pointer crosses the
    // midline toward that neighbour; -1 while still on the start island's side.
    function pendingFromDrag(from, pt) {
        const A = state.islands[from];
        const ax = cx(A.c), ay = cy(A.r);
        const dx = pt.x - ax, dy = pt.y - ay;
        if (Math.hypot(dx, dy) < state.cs * 0.3) return -1;
        const dir = Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'R' : 'L') : (dy > 0 ? 'D' : 'U');
        const e = state.dirEdge[from][dir];
        if (e === undefined) return -1;
        if (crossingBlocked(e)) return -1; // dragging toward a crossed-out corridor does nothing
        const ed = state.G.edges[e], nb = ed.a === from ? ed.b : ed.a;
        const vx = cx(state.islands[nb].c) - ax, vy = cy(state.islands[nb].r) - ay, L2 = (vx * vx + vy * vy) || 1;
        const t = (dx * vx + dy * vy) / L2;
        return t >= 0.5 ? e : -1; // past the midline between the two islands
    }

    function onPointerDown(ev) {
        if (!state.puzzle || state.won) return;
        const btn = ev.button;
        if (btn !== undefined && btn !== 0 && btn !== 2) return; // left / right only
        const pt = eventToPoint(ev); if (!pt) return;
        const button = btn === 2 ? 2 : 0;
        let drag = null;
        const from = nearestIsland(pt);
        if (from >= 0) drag = { pointerId: ev.pointerId, button, from, pending: -1, mode: 'island', moved: false, sx: pt.x, sy: pt.y };
        else { const e = edgeAtPoint(pt); if (e >= 0) drag = { pointerId: ev.pointerId, button, edge: e, mode: 'bridge' }; }
        if (!drag) return;
        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        clearHint();
        state.dragging = drag;
        if (drag.mode === 'island') repaint(); // light up the start island
    }
    function setHover(edge, isle) {
        edge = edge == null ? -1 : edge; isle = isle == null ? -1 : isle;
        if (edge === state.hoverEdge && isle === state.hoverIsland) return;
        state.hoverEdge = edge; state.hoverIsland = isle; repaint();
    }
    function onPointerMove(ev) {
        const d = state.dragging;
        if (d) {
            if (ev.pointerId !== d.pointerId || d.mode !== 'island') return;
            const pt = eventToPoint(ev); if (!pt) return;
            if (!d.moved && Math.hypot(pt.x - d.sx, pt.y - d.sy) > state.cs * 0.25) d.moved = true;
            const pend = pendingFromDrag(d.from, pt);
            if (pend !== d.pending) { d.pending = pend; repaint(); }
            return;
        }
        // Hover preview — mouse only (touch has no hover).
        if (ev.pointerType && ev.pointerType !== 'mouse') return;
        if (!state.puzzle || state.won) { setHover(-1, -1); return; }
        const pt = eventToPoint(ev);
        if (!pt) { setHover(-1, -1); return; }
        if (state.mode === 'build') { setHover(edgeAtPoint(pt), -1); return; } // bridge preview
        // Mark mode: previewing a corridor to confirm, or an island to flag handled.
        const isl = nearestIsland(pt);
        if (isl >= 0) setHover(-1, isl);
        else setHover(edgeAtPoint(pt), -1);
    }
    function onPointerEnd(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        try { board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        state.dragging = null;
        const mark = state.mode === 'mark';
        if (d.mode === 'bridge') { if (mark) toggleEdgeMark(d.edge); else cycleEdge(d.edge, d.button); return; }
        if (d.pending >= 0) { if (mark) toggleEdgeMark(d.pending); else cycleEdge(d.pending, d.button); return; } // dragged island → island
        if (!d.moved && mark) { toggleDone(d.from); return; } // tapping an island flags it handled — Mark mode only
        repaint(); // no action (e.g. an island tap in Build mode) — clear the active highlight
    }

    // A bridge here would cross one that's already on the board (two bridges may
    // never cross), so placing it is simply refused rather than flagged after.
    function crossingBlocked(e) {
        for (const f of state.G.cross[e]) if (state.edgeVal[f] >= 1) return true;
        return false;
    }

    // Left cycles up (0→1→2→0); right cycles down (0→2→1→0).
    function cycleEdge(e, button) {
        const v = state.edgeVal[e];
        const nv = button === 2 ? (v + 2) % 3 : (v + 1) % 3;
        if (nv >= 1 && crossingBlocked(e)) return; // safety: crossed-out corridors are inert
        pushUndo();
        state.edgeVal[e] = nv;
        state.edgeMark[e] = 0; // changing the count drops any prior "confirmed" mark
        state.lastEdge = e;    // the win pop radiates out from here
        const { a, b } = state.G.edges[e];
        state.doneMark[a] = 0; state.doneMark[b] = 0; // editing a connection un-completes its islands
        afterChange();
    }

    // Toggle the "I'm sure of this corridor's count" annotation (0/1/2). Like the
    // island done-flag it's a personal memo — undoable, and it never affects the
    // puzzle. Corridors an existing bridge crosses can't be marked.
    function toggleEdgeMark(e) {
        if (crossingBlocked(e)) return;
        pushUndo();
        state.edgeMark[e] ^= 1;
        repaint();
        updateUndoButton();
    }

    function setMode(m) {
        if (m !== 'build' && m !== 'mark') return;
        state.mode = m;
        const tools = document.getElementById('hashi-tools');
        if (tools) for (const b of tools.querySelectorAll('.hashi-tool')) {
            const on = b.dataset.mode === m;
            b.classList.toggle('active', on);
            b.setAttribute('aria-checked', on ? 'true' : 'false');
        }
        setHover(-1);
    }

    // Flag an island "complete". It doesn't affect the puzzle (undoable memo), but
    // it's only allowed once the island's number is satisfied — and marking it then
    // confirms (greys) every one of its connections in one go. Tapping it again
    // clears just the island flag.
    function toggleDone(v) {
        if (state.doneMark[v]) {
            pushUndo();
            state.doneMark[v] = 0;
            repaint(); updateUndoButton();
            return;
        }
        if (islandSum(v) !== state.needs[v]) {
            if (PC.toast) PC.toast.show(PC.i18n.t('hashiMarkNeedsFull'));
            return;
        }
        pushUndo();
        state.doneMark[v] = 1;
        for (const e of state.G.incident[v]) if (!crossingBlocked(e)) state.edgeMark[e] = 1; // lock all its connections
        repaint(); updateUndoButton();
    }

    function afterChange() {
        refreshViolationsOnEdit();
        repaint();
        if (!state.won && rulesSatisfied()) {
            state.won = true;
            // Drop any hover so a later mouse-move's hover-clear can't repaint the
            // board and restart the win pop (which looked like a second bounce).
            state.hoverEdge = -1; state.hoverIsland = -1;
            shell.markSolved();
            clearViolations();
            clearHint();
            const rl = board.querySelector('#hashi-reveal'); if (rl) while (rl.firstChild) rl.removeChild(rl.firstChild);
            repaint();
        }
        updateStatusRow();
        updateUndoButton();
    }
    function updateStatusRow() { shell.setWin(state.won); updateViolationPill(); }

    // -----------------------------------------------------------------
    // Undo
    // -----------------------------------------------------------------
    function snapshotState() { return { edgeVal: state.edgeVal.slice(), edgeMark: state.edgeMark.slice(), doneMark: state.doneMark.slice() }; }
    function restoreSnapshot(snap) {
        const wasWon = state.won;
        state.edgeVal = snap.edgeVal.slice();
        if (snap.edgeMark) state.edgeMark = snap.edgeMark.slice();
        if (snap.doneMark) state.doneMark = snap.doneMark.slice();
        state.dragging = null; state.won = false;
        if (wasWon) shell.clearWin();
        showAllViolationsNow();
        clearHint(); repaint(); updateStatusRow();
    }
    function pushUndo() { if (undoHistory && !state.won) { undoHistory.push(); updateUndoButton(); } }
    function doUndo() { if (state.puzzle && undoHistory && undoHistory.undo()) updateUndoButton(); }
    function updateUndoButton() { const btn = document.getElementById('undo-btn'); if (btn) btn.disabled = !(undoHistory && undoHistory.canUndo()); }

    // -----------------------------------------------------------------
    // Hints
    // -----------------------------------------------------------------
    // Action phrasing for a forced edge value (verb form) and an assumed value.
    // `atLeast` turns an exact count into a lower bound ("at least one bridge").
    const n2En = (v) => (v === 2 ? 'two' : 'one');
    const n2Zh = (v) => (v === 2 ? '兩' : '一');
    const actEn = (v, atLeast) => (v === 0 ? 'stay empty' : `${atLeast ? 'take at least ' : 'take '}${n2En(v)} bridge${v === 2 ? 's' : ''}`);
    const asmEn = (v) => (v === 0 ? 'no bridge' : v === 2 ? 'two bridges' : 'one bridge');
    const actZh = (v, atLeast) => (v === 0 ? '留空' : `${atLeast ? '至少' : ''}架${n2Zh(v)}座橋`);
    const asmZh = (v) => (v === 0 ? '不架橋' : v === 2 ? '架兩座橋' : '架一座橋');
    const HINT_TEXTS = {
        en: {
            conflict: (h) => h.cross && h.over
                ? 'The highlighted parts break a rule — bridges cross, and an island has too many bridges.'
                : h.cross
                    ? 'The highlighted bridges cross each other — bridges may never cross.'
                    : 'The highlighted island has more bridges than its number allows.',
            wrong: 'The highlighted bridge(s) disagree with the unique solution — remove or re-count them.',
            degree: (h) => {
                const s = h.src;
                if (!s) return `The nearby numbers and the bridges already drawn force the highlighted connection to ${actEn(h.value, h.atLeast)}.`;
                if (s.kind === 'sole') return `The circled ${s.need} has neighbours in only one direction, so all ${s.need} of its bridges must go along this one connection.`;
                if (s.kind === 'onlyLeft') return `The circled ${s.need} already has ${s.have}; only one direction is left, so the remaining ${s.remaining} must go here.`;
                if (s.kind === 'saturate') return `The circled ${s.need} exactly fills all ${s.open} of its directions, so each one must take two bridges.`;
                if (s.kind === 'saturateRest') return `The circled ${s.need} already has ${s.have}; its remaining ${s.remaining} has to fill ${s.open} directions, so each of them takes two bridges.`;
                if (s.kind === 'eachOne') return `The circled ${s.need} has ${s.open} open directions: leaving any of them empty caps the island at ${s.need - 1} bridges, short of ${s.need}, so every direction must take at least one bridge.`;
                if (s.kind === 'atleast') return `The circled ${s.need}: its other directions can absorb at most ${s.otherMax} more, so the remaining ${s.add} has to run through here — ${actEn(s.value, h.atLeast)}.`;
                return `The circled ${s.need} already has ${s.have}, which forces this connection to ${actEn(s.value, h.atLeast)}.`;
            },
            cut: (h) => {
                const n = (h.anchor && h.anchor.islands && h.anchor.islands.length) || 0;
                return `Without a bridge here, ${n > 1 ? `those ${n} circled islands have` : 'the circled island has'} no other way to reach the rest of the network, so this connection must take at least one bridge.`;
            },
            deep: (h) => {
                const brk = h.bad && h.bad.kind === 'cross' ? 'two bridges would be forced to cross'
                    : h.bad && h.bad.kind === 'disconnect' ? 'an island could no longer connect'
                        : 'an island couldn’t reach its number';
                const lead = h.chain && h.chain.length ? 'the numbered steps are forced and ' : '';
                return `Assume the dashed connection takes ${asmEn(h.assume.value)}: ${lead}${brk} (circled). So it must ${actEn(h.value)}.`;
            },
            none: 'Nothing more to deduce right now.',
        },
        zh: {
            conflict: (h) => h.cross && h.over
                ? '醒目處違反了規則——有橋交叉，且有島的橋數超過它的數字。'
                : h.cross
                    ? '醒目的橋互相交叉了——橋絕不能交叉。'
                    : '醒目的島橋數超過它的數字了。',
            wrong: '醒目的橋與唯一解不符——請移除或重算它們。',
            degree: (h) => {
                const s = h.src;
                if (!s) return `綜合鄰近幾座島的數字與已畫的橋，可推出醒目的這條${h.atLeast ? '至少還要' : '必須'}${actZh(h.value, false)}。`;
                if (s.kind === 'sole') return `圈起來的 ${s.need} 只有一個方向有鄰居，所以它的 ${s.need} 座橋只能全部連往這條。`;
                if (s.kind === 'onlyLeft') return `圈起來的 ${s.need} 已接 ${s.have} 座，只剩一個方向還沒連，所以剩下的 ${s.remaining} 座只能走這條。`;
                if (s.kind === 'saturate') return `圈起來的 ${s.need} 剛好要填滿它全部 ${s.open} 個方向，所以每個方向都必須各架兩座橋。`;
                if (s.kind === 'saturateRest') return `圈起來的 ${s.need} 已接 ${s.have} 座，剩下的 ${s.remaining} 座要填滿 ${s.open} 個方向，所以每個方向都必須各架兩座橋。`;
                if (s.kind === 'eachOne') return `圈起來的 ${s.need} 有 ${s.open} 個可連方向：只要任一個空著，全島最多只能連到 ${s.need - 1} 座，湊不滿 ${s.need}，所以每個方向都至少要有一座橋。`;
                if (s.kind === 'atleast') return `圈起來的 ${s.need}：其他方向最多只能再接 ${s.otherMax} 座，還差 ${s.add} 座一定得走這條，所以這條${actZh(s.value, h.atLeast)}。`;
                return `圈起來的 ${s.need} 已接 ${s.have} 座，推得這條${actZh(s.value, h.atLeast)}。`;
            },
            cut: (h) => {
                const n = (h.anchor && h.anchor.islands && h.anchor.islands.length) || 0;
                return `若這條不架橋，圈起來的${n > 1 ? `這 ${n} 座島` : '島'}就沒有別的路能連到其餘的島，所以這條至少要架一座橋。`;
            },
            deep: (h) => {
                const brk = h.bad && h.bad.kind === 'cross' ? '會逼出兩橋交叉'
                    : h.bad && h.bad.kind === 'disconnect' ? '會有島連不起來'
                        : '會有島的橋數湊不出來';
                const lead = h.chain && h.chain.length ? '順著編號的幾步，' : '';
                return `假設虛線這條${asmZh(h.assume.value)}：${lead}${brk}（圈起來處）。所以它必須${actZh(h.value)}。`;
            },
            none: '目前沒有可推的下一步。',
        },
    };
    function hintTexts() { const l = (PC.i18n && PC.i18n.locale) || 'en'; return HINT_TEXTS[l] || HINT_TEXTS.en; }

    function computeHint() {
        const v = computeViolations();
        if (v.over.length || v.cross.length) {
            const edges = [], isles = [];
            for (const [i, j] of v.cross) { edges.push(i); edges.push(j); }
            for (const w of v.over) isles.push(w);
            return { kind: 'conflict', edges, isles, cross: v.cross.length > 0, over: v.over.length > 0 };
        }
        // Wrong = an OVER-placed bridge (more than the solution has here). A pair
        // built only part-way (one bridge where two are needed) is just unfinished,
        // not wrong, so it isn't flagged.
        const wrong = [];
        for (let e = 0; e < state.G.edges.length; e++) if (state.edgeVal[e] > state.solVal[e]) wrong.push(e);
        if (wrong.length) return { kind: 'wrong', edges: wrong };
        // Hints read the player's drawn bridges as lower bounds, so half-built pairs
        // are fine and "add at least one bridge here" moves can surface.
        const drawn = state.edgeVal;
        const step = HS.nextStep(state.G, state.needs, drawn);
        // A big connectivity (cut) strand is hard to verify at a glance ("those N
        // islands have no other route"). Show it instead as an assume→contradiction
        // walk-through with numbered steps, so there's an order to follow. Small,
        // obvious strands keep the one-line cut.
        if (step && step.reason === 'cut' && step.anchor && step.anchor.islands && step.anchor.islands.length > 2 && HS.refuteEmpty) {
            const ref = HS.refuteEmpty(state.G, state.needs, drawn, step.edge);
            if (ref) return { kind: 'deep', edge: step.edge, value: step.value, assume: { edge: step.edge, value: 0 }, chain: ref.chain, bad: ref.bad };
        }
        if (step) return { kind: 'deduce', edge: step.edge, value: step.value, atLeast: step.atLeast, reason: step.reason, anchor: step.anchor, src: step.src };
        const deep = HS.nextStepDeep(state.G, state.needs, drawn);
        if (deep) return { kind: 'deep', edge: deep.edge, value: deep.value, assume: deep.assume, chain: deep.chain, bad: deep.bad };
        return null;
    }

    // Console dump of a hint's full reasoning + a reproducible board snapshot.
    function logHint(h) {
        const isl = (v) => `#${v}(r${state.islands[v].r}c${state.islands[v].c}=${state.needs[v]})`;
        const edg = (e) => { const { a, b } = state.G.edges[e]; return isl(a) + '—' + isl(b); };
        const L = ['[HASHI HINT] kind=' + h.kind + (h.reason ? ' reason=' + h.reason : '')];
        if (h.edge != null) L.push('forced: ' + edg(h.edge) + ' = ' + h.value);
        if (h.src) L.push('src: ' + JSON.stringify(Object.assign({}, h.src, { island: h.src.island != null ? isl(h.src.island) : undefined, isles: (h.src.isles || []).map(isl), stranded: (h.src.stranded || []).map(isl) })));
        if (h.anchor) L.push('anchor: ' + JSON.stringify({ islands: (h.anchor.islands || []).map(isl), edges: (h.anchor.edges || []).map(edg) }));
        if (h.assume) L.push('assume: ' + edg(h.assume.edge) + ' = ' + h.assume.value);
        if (h.chain) L.push('chain: [' + h.chain.map((s) => edg(s.edge) + '=' + s.value).join(', ') + ']');
        if (h.bad) { const b = h.bad; L.push('breaks: ' + b.kind + (b.island != null ? ' @' + isl(b.island) : '') + (b.islands ? ' @' + b.islands.map(isl).join(',') : '') + (b.edges ? ' @' + b.edges.map(edg).join(',') : '') + (b.edge != null ? ' @' + edg(b.edge) : '')); }
        const drawn = [];
        for (let e = 0; e < state.G.edges.length; e++) if (state.edgeVal[e] >= 1) drawn.push([state.G.edges[e].a, state.G.edges[e].b, state.edgeVal[e]]);
        L.push('board: ' + JSON.stringify({ size: state.N, islands: state.islands.map((i) => [i.r, i.c, i.need]), drawn }));
        console.log(L.join('\n  '));
    }

    function showHint() {
        if (!state.puzzle || state.won) return;
        if (state.hint) { clearHint(); return; }
        const h = computeHint();
        if (DEBUG && h) logHint(h);
        if (!h) { state.hint = { kind: 'none' }; renderHintBanner(); return; }
        state.hint = h; renderHintBanner(); repaintHint();
    }
    function clearHint() {
        if (!state.hint && state.hintBanner && state.hintBanner.hidden) return;
        state.hint = null;
        if (state.hintBanner) { state.hintBanner.hidden = true; state.hintBanner.textContent = ''; state.hintBanner.classList.remove('error'); }
        repaintHint();
    }
    function renderHintBanner() {
        const h = state.hint; if (!h || !state.hintBanner) return;
        const t = hintTexts();
        let html;
        if (h.kind === 'conflict') html = t.conflict(h);
        else if (h.kind === 'wrong') html = t.wrong;
        else if (h.kind === 'none') html = t.none;
        else if (h.kind === 'deep') html = t.deep(h);
        else if (h.reason === 'cut') html = t.cut(h);
        else html = t.degree(h);
        state.hintBanner.innerHTML = html;
        if (PC.icons && PC.icons.render) PC.icons.render(state.hintBanner);
        state.hintBanner.classList.toggle('error', h.kind === 'wrong' || h.kind === 'conflict');
        state.hintBanner.hidden = false;
    }
    function repaintHint() {
        const layer = board && board.querySelector('#hashi-hint');
        if (!layer) return;
        // keep any pending-drag preview; clear only hint marks
        Array.from(layer.querySelectorAll('.hashi-hint-mark')).forEach((n) => n.remove());
        const h = state.hint; if (!h || h.kind === 'none') return;
        const { cs } = state;
        const sw = Math.max(2, cs * 0.07), offUnit = Math.max(2.2, cs * 0.1);
        const ringIsland = (v, cls) => {
            const is = state.islands[v];
            layer.appendChild(PC.svgEl('circle', { class: cls + ' hashi-hint-mark', cx: cx(is.c), cy: cy(is.r), r: cs * 0.44 }));
        };
        const bandEdge = (e, cls) => {
            const { a, b } = state.G.edges[e], A = state.islands[a], B = state.islands[b];
            layer.appendChild(PC.svgEl('line', { class: cls + ' hashi-hint-mark', 'stroke-width': Math.max(sw + 4, cs * 0.18), 'stroke-linecap': 'round', x1: cx(A.c), y1: cy(A.r), x2: cx(B.c), y2: cy(B.r) }));
        };
        const ghostEdge = (e, value, cls) => {
            const g = PC.svgEl('g', { class: 'hashi-hint-mark' });
            drawBridge(g, e, value || 1, cls || 'hashi-bridge hashi-hint-ghost', sw, offUnit);
            layer.appendChild(g);
        };
        const stepNum = (e, n) => {
            const { a, b } = state.G.edges[e], A = state.islands[a], B = state.islands[b];
            const t = PC.svgEl('text', {
                class: 'hashi-hint-step hashi-hint-mark', x: (cx(A.c) + cx(B.c)) / 2, y: (cy(A.r) + cy(B.r)) / 2,
                'text-anchor': 'middle', 'dominant-baseline': 'middle', 'font-size': Math.max(10, Math.round(cs * 0.3)),
            });
            t.textContent = String(n); layer.appendChild(t);
        };
        const badMark = (bad) => {
            if (!bad) return;
            if (bad.kind === 'degree' && typeof bad.island === 'number') ringIsland(bad.island, 'hashi-hint-ring wrong');
            else if (bad.kind === 'cross' && bad.edges) for (const e of bad.edges) bandEdge(e, 'hashi-hint-band wrong');
            else if (bad.kind === 'disconnect') {
                if (bad.islands) for (const v of bad.islands) ringIsland(v, 'hashi-hint-ring wrong');
                if (typeof bad.edge === 'number') bandEdge(bad.edge, 'hashi-hint-band wrong');
            }
        };

        if (h.kind === 'conflict') {
            for (const e of h.edges) bandEdge(e, 'hashi-hint-band wrong');
            for (const w of h.isles) ringIsland(w, 'hashi-hint-ring wrong');
            return;
        }
        if (h.kind === 'wrong') { for (const e of h.edges) bandEdge(e, 'hashi-hint-band wrong'); return; }
        if (h.kind === 'deep') {
            // the refuted assumption (dashed red + red ghost), the forced numbered
            // steps it triggers, and where the rule finally breaks.
            bandEdge(h.edge, 'hashi-hint-assume');
            if (h.assume.value >= 1) ghostEdge(h.edge, h.assume.value, 'hashi-bridge bad hashi-hint-ghost');
            let n = 0;
            if (h.chain) for (const st of h.chain) if (st.value >= 1) { ghostEdge(st.edge, st.value); stepNum(st.edge, ++n); }
            badMark(h.bad);
            return;
        }
        // deduce. Saturate decides the whole fan at once: band + ghost every open
        // connection of the circled island (each two bridges) and ring the
        // neighbours it reaches. Otherwise just band + ghost the one forced edge.
        if (h.src && h.src.fan) {
            for (const f of h.src.fan) { bandEdge(f.edge, 'hashi-hint-band'); ghostEdge(f.edge, f.value); }
            if (h.src.isles) for (const w of h.src.isles) ringIsland(w, 'hashi-hint-context');
            if (h.anchor && h.anchor.islands) for (const v of h.anchor.islands) ringIsland(v, 'hashi-hint-anchor');
            return;
        }
        if (h.anchor) {
            if (h.anchor.islands) for (const v of h.anchor.islands) ringIsland(v, 'hashi-hint-anchor');
            if (h.anchor.edges) for (const e of h.anchor.edges) bandEdge(e, 'hashi-hint-source');
        }
        bandEdge(h.edge, 'hashi-hint-band');
        if (h.value >= 1) ghostEdge(h.edge, h.value);
    }

    // -----------------------------------------------------------------
    // Toolbar actions
    // -----------------------------------------------------------------
    async function startNewGame() {
        const seed = (pendingSeed != null) ? pendingSeed
            : ((Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0);
        pendingSeed = null;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        parsePuzzle(state.puzzle);
        state.dragging = null; state.won = false; state.hint = null;
        clearViolations();
        if (undoHistory) undoHistory.clear();
        renderBoard();
        updateStatusRow(); updateUndoButton();
        if (PC.share) PC.share.replaceUrl({ size: shell.size, difficulty: shell.difficulty, seed });
    }
    function resetBoard() {
        if (!state.puzzle) return;
        if (state.won) { if (undoHistory) undoHistory.clear(); } else pushUndo();
        state.edgeVal = new Int8Array(state.G.edges.length);
        state.edgeMark = new Int8Array(state.G.edges.length);
        state.doneMark = new Int8Array(state.islands.length);
        state.won = false; clearViolations(); clearHint(); repaint(); updateStatusRow(); updateUndoButton();
    }
    function onReveal() {
        const layer = board && board.querySelector('#hashi-reveal');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        if (shell.revealed && !state.won) {
            const sw = Math.max(2, state.cs * 0.07), offUnit = Math.max(2.2, state.cs * 0.1);
            for (let e = 0; e < state.G.edges.length; e++) if (state.solVal[e] >= 1) drawBridge(layer, e, state.solVal[e], 'hashi-reveal-line', sw, offUnit);
        }
        repaintHint();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------
    function init() {
        shell = PC.shell.create({
            gameId: 'hashi',
            difficulty: { default: urlInitial ? urlInitial.difficulty : 'medium' },
            size: { kind: 'slider', values: SIZE_STEPS, min: MIN_SIZE, max: MAX_SIZE, default: urlInitial ? urlInitial.size : 11 },
            onNewGame: startNewGame,
            onReset: resetBoard,
            onReveal: onReveal,
        });
        board = shell.dom.board;
        state.hintBanner = document.getElementById('hint-banner');
        undoHistory = PC.history.create({ limit: 20, snapshot: snapshotState, restore: restoreSnapshot });

        const shareBtn = document.getElementById('share-btn');
        if (shareBtn) shareBtn.addEventListener('click', onShareClick);
        const undoBtn = document.getElementById('undo-btn');
        if (undoBtn) undoBtn.addEventListener('click', doUndo);
        const hintBtn = document.getElementById('hint-btn');
        if (hintBtn) hintBtn.addEventListener('click', showHint);

        const tools = document.getElementById('hashi-tools');
        if (tools) tools.addEventListener('click', (ev) => {
            const btn = ev.target.closest('.hashi-tool');
            if (btn && btn.dataset.mode) setMode(btn.dataset.mode);
        });

        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerEnd);
        board.addEventListener('pointercancel', onPointerEnd);
        board.addEventListener('pointerleave', () => setHover(-1));
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());

        if (PC.i18n && typeof PC.i18n.subscribe === 'function') {
            PC.i18n.subscribe(() => { if (state.hint) renderHintBanner(); });
        }
        window.addEventListener('keydown', (ev) => {
            if ((ev.ctrlKey || ev.metaKey) && !ev.shiftKey && !ev.altKey && (ev.key === 'z' || ev.key === 'Z')) { doUndo(); ev.preventDefault(); }
        });

        shell.start();
    }

    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
})();
