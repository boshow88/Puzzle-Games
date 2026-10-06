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
    const UNKNOWN = HS.UNKNOWN;

    const SIZE_STEPS = [7, 9, 11, 13, 15];
    const MIN_SIZE = 7, MAX_SIZE = 15;
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
        dirEdge: null,          // per island: {U,D,L,R} → edge index
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
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);
        svg.appendChild(PC.svgEl('rect', { class: 'hashi-bg', x: 0, y: 0, width: BOARD, height: BOARD }));
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

    function drawBridge(layer, e, val, cls, sw, offUnit) {
        const { a, b } = state.G.edges[e];
        const A = state.islands[a], B = state.islands[b];
        if (val === 1) {
            layer.appendChild(bridgeLine(cls, A.r, A.c, B.r, B.c, 0, sw));
        } else if (val === 2) {
            layer.appendChild(bridgeLine(cls, A.r, A.c, B.r, B.c, -offUnit, sw));
            layer.appendChild(bridgeLine(cls, A.r, A.c, B.r, B.c, offUnit, sw));
        }
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
        // Bridges
        for (let e = 0; e < G.edges.length; e++) {
            if (state.edgeVal[e] < 1) continue;
            const bad = !won && crossSet.has(e);
            drawBridge(bl, e, state.edgeVal[e], 'hashi-bridge' + (bad ? ' bad' : '') + (won ? ' won' : ''), sw, offUnit);
        }
        // Islands
        const rad = cs * 0.34;
        const font = Math.max(11, Math.round(cs * 0.4));
        for (let v = 0; v < G.islands.length; v++) {
            const is = state.islands[v];
            const sum = islandSum(v);
            const done = sum === state.needs[v];
            const over = !won && overSet.has(v);
            const g = PC.svgEl('g', { class: 'hashi-island' + (done ? ' done' : '') + (over ? ' bad' : '') + (won ? ' won' : '') });
            g.appendChild(PC.svgEl('circle', { class: 'hashi-isle-disc', cx: cx(is.c), cy: cy(is.r), r: rad }));
            const t = PC.svgEl('text', {
                class: 'hashi-isle-num', x: cx(is.c), y: cy(is.r),
                'text-anchor': 'middle', 'dominant-baseline': 'middle', dy: '0.08em', 'font-size': font,
            });
            t.textContent = String(state.needs[v]);
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
    function pendingFromDrag(from, pt) {
        const A = state.islands[from];
        const dx = pt.x - cx(A.c), dy = pt.y - cy(A.r);
        if (Math.hypot(dx, dy) < state.cs * 0.4) return -1; // still on the island
        const dir = Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'R' : 'L') : (dy > 0 ? 'D' : 'U');
        const e = state.dirEdge[from][dir];
        return (e === undefined) ? -1 : e;
    }

    function onPointerDown(ev) {
        if (!state.puzzle || state.won) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        const pt = eventToPoint(ev); if (!pt) return;
        const from = nearestIsland(pt);
        if (from < 0) return;
        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        clearHint();
        state.dragging = { pointerId: ev.pointerId, from, pending: -1 };
        paintPending();
    }
    function onPointerMove(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        const pt = eventToPoint(ev); if (!pt) return;
        const pend = pendingFromDrag(d.from, pt);
        if (pend !== d.pending) { d.pending = pend; paintPending(); }
    }
    function onPointerEnd(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        try { board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        const pend = d.pending;
        state.dragging = null;
        clearPending();
        if (pend >= 0) cycleEdge(pend);
    }

    function cycleEdge(e) {
        pushUndo();
        state.edgeVal[e] = (state.edgeVal[e] + 1) % 3;
        afterChange();
    }

    function paintPending() {
        clearPending();
        const d = state.dragging; if (!d || d.pending < 0) return;
        const layer = board.querySelector('#hashi-hint'); if (!layer) return;
        const sw = Math.max(2, state.cs * 0.07);
        const next = (state.edgeVal[d.pending] + 1) % 3;
        const g = PC.svgEl('g', { class: 'hashi-pending' });
        if (next === 0) {
            // previewing removal: faint dashed through the corridor
            drawBridge(g, d.pending, Math.max(1, state.edgeVal[d.pending]), 'hashi-pending-line erase', sw, Math.max(2.2, state.cs * 0.1));
        } else {
            drawBridge(g, d.pending, next, 'hashi-pending-line', sw, Math.max(2.2, state.cs * 0.1));
        }
        layer.appendChild(g);
    }
    function clearPending() {
        const layer = board && board.querySelector('#hashi-hint');
        if (!layer) return;
        const p = layer.querySelector('.hashi-pending');
        if (p) layer.removeChild(p);
    }

    function afterChange() {
        refreshViolationsOnEdit();
        repaint();
        if (!state.won && rulesSatisfied()) {
            state.won = true;
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
    function snapshotState() { return { edgeVal: state.edgeVal.slice() }; }
    function restoreSnapshot(snap) {
        const wasWon = state.won;
        state.edgeVal = snap.edgeVal.slice();
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
    const HINT_TEXTS = {
        en: {
            conflict: (h) => h.cross && h.over
                ? 'The highlighted parts break a rule — bridges cross, and an island has too many bridges.'
                : h.cross
                    ? 'The highlighted bridges cross each other — bridges may never cross.'
                    : 'The highlighted island has more bridges than its number allows.',
            wrong: 'The highlighted bridge(s) disagree with the unique solution — remove or re-count them.',
            degree: (n) => `An island’s number forces it: the highlighted connection must carry ${n === 2 ? 'two bridges' : 'one bridge'}.`,
            cross: 'A bridge already placed rules this one out, so the highlighted connection stays empty.',
            cut: 'Without the highlighted bridge an island could never connect, so it must be built.',
            deep: (h) => `Assume the highlighted connection takes ${h.assume.value === 0 ? 'no bridge' : h.assume.value + ' bridge(s)'} and it leads to a dead end — so it must take ${h.value} bridge(s).`,
            none: 'Nothing more to deduce right now.',
        },
        zh: {
            conflict: (h) => h.cross && h.over
                ? '醒目處違反了規則——有橋交叉，且有島的橋數超過它的數字。'
                : h.cross
                    ? '醒目的橋互相交叉了——橋絕不能交叉。'
                    : '醒目的島橋數超過它的數字了。',
            wrong: '醒目的橋與唯一解不符——請移除或重算它們。',
            degree: (n) => `島上的數字逼出:醒目的這條連線必須架 ${n === 2 ? '兩座橋' : '一座橋'}。`,
            cross: '已架的橋排除了這條,所以醒目的連線維持空白。',
            cut: '少了醒目的這座橋,就有島永遠連不進來,所以它一定要架。',
            deep: (h) => `假設醒目的連線架 ${h.assume.value === 0 ? '零座橋' : h.assume.value + ' 座橋'},會走進死路——所以它必須架 ${h.value} 座橋。`,
            none: '目前沒有可推的下一步。',
        },
    };
    function hintTexts() { const l = (PC.i18n && PC.i18n.locale) || 'en'; return HINT_TEXTS[l] || HINT_TEXTS.en; }

    function playerCur() {
        const E = state.G.edges.length;
        const cur = new Int8Array(E);
        for (let e = 0; e < E; e++) cur[e] = state.edgeVal[e] >= 1 ? state.edgeVal[e] : UNKNOWN;
        return cur;
    }

    function computeHint() {
        const v = computeViolations();
        if (v.over.length || v.cross.length) {
            const edges = [], isles = [];
            for (const [i, j] of v.cross) { edges.push(i); edges.push(j); }
            for (const w of v.over) isles.push(w);
            return { kind: 'conflict', edges, isles, cross: v.cross.length > 0, over: v.over.length > 0 };
        }
        // wrong: a bridge the player drew that disagrees with the solution
        const wrong = [];
        for (let e = 0; e < state.G.edges.length; e++) if (state.edgeVal[e] >= 1 && state.edgeVal[e] !== state.solVal[e]) wrong.push(e);
        if (wrong.length) return { kind: 'wrong', edges: wrong };
        const cur = playerCur();
        const step = HS.nextStep(state.G, state.needs, cur);
        if (step) return { kind: 'deduce', edge: step.edge, value: step.value, reason: step.reason };
        const deep = HS.nextStepDeep(state.G, state.needs, cur);
        if (deep) return { kind: 'deep', edge: deep.edge, value: deep.value, assume: deep.assume };
        return null;
    }

    function showHint() {
        if (!state.puzzle || state.won) return;
        if (state.hint) { clearHint(); return; }
        const h = computeHint();
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
        else if (h.reason === 'cross') html = t.cross;
        else if (h.reason === 'cut') html = t.cut;
        else html = t.degree(h.value);
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
        const ringIsland = (v, wrong) => {
            const is = state.islands[v];
            layer.appendChild(PC.svgEl('circle', { class: 'hashi-hint-ring' + (wrong ? ' wrong' : '') + ' hashi-hint-mark', cx: cx(is.c), cy: cy(is.r), r: cs * 0.44 }));
        };
        const markEdge = (e, cls) => {
            const g = PC.svgEl('g', { class: 'hashi-hint-mark' });
            // draw a highlight band along the corridor
            const { a, b } = state.G.edges[e];
            const A = state.islands[a], B = state.islands[b];
            g.appendChild(PC.svgEl('line', { class: cls, 'stroke-width': Math.max(sw + 4, cs * 0.18), 'stroke-linecap': 'round', x1: cx(A.c), y1: cy(A.r), x2: cx(B.c), y2: cy(B.r) }));
            layer.appendChild(g);
        };
        if (h.kind === 'conflict') {
            for (const e of h.edges) markEdge(e, 'hashi-hint-band wrong');
            for (const w of h.isles) ringIsland(w, true);
            return;
        }
        if (h.kind === 'wrong') { for (const e of h.edges) markEdge(e, 'hashi-hint-band wrong'); return; }
        if (h.kind === 'deep') {
            markEdge(h.edge, 'hashi-hint-band');
            // ghost the forced bridges
            const gg = PC.svgEl('g', { class: 'hashi-hint-mark' });
            drawBridge(gg, h.edge, h.value || 1, 'hashi-bridge hashi-hint-ghost', sw, offUnit);
            layer.appendChild(gg);
            return;
        }
        // deduce
        markEdge(h.edge, 'hashi-hint-band');
        if (h.value >= 1) {
            const gg = PC.svgEl('g', { class: 'hashi-hint-mark' });
            drawBridge(gg, h.edge, h.value, 'hashi-bridge hashi-hint-ghost', sw, offUnit);
            layer.appendChild(gg);
        }
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
            size: { kind: 'slider', values: SIZE_STEPS, min: MIN_SIZE, max: MAX_SIZE, default: urlInitial ? urlInitial.size : 9 },
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

        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerEnd);
        board.addEventListener('pointercancel', onPointerEnd);
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
