/**
 * Guards (Akari reskin) — game UI.
 *
 * Consumes window.PuzzleGenerators.lightup + the shared shell. Input mirrors
 * Nonogram's four modes (Cycle / Guard / Mark ✗ / Erase): a tap cycles/toggles a
 * floor cell, a drag paints the content decided by its start cell. A guard
 * watches its row/column until a wall (pillar); win when every floor cell is
 * watched, no two guards see each other, and every numbered pillar is exact.
 * (Internally the emitter is still called "bulb"/BULB — the Akari core.)
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;
    const LU = window.PuzzleSolvers.lightup;
    const EMITTER_ICON = 'user'; // the guard symbol (theme: Guards)
    const BOARD = 480;
    const VIOLATION_DELAY_MS = 800; // defer red conflict marks while a cell is being cycled

    // Player marks (chosen so they equal the solver's UNKNOWN/BULB/NOBULB).
    const EMPTY = 0, BULB = 1, XMARK = 2;

    const VALID_MODES = ['cycle', 'bulb', 'block', 'empty'];
    function resolveTarget(mode, cur) {
        // Cycle follows the toolbar order: empty → guard → ✗ → empty.
        if (mode === 'cycle') return cur === EMPTY ? BULB : cur === BULB ? XMARK : EMPTY;
        if (mode === 'bulb') return cur === BULB ? EMPTY : BULB;
        if (mode === 'block') return cur === XMARK ? EMPTY : XMARK;
        return EMPTY; // 'empty' = erase
    }

    const MIN_SIZE = 6, MAX_SIZE = 25;
    const SIZE_STEPS = [6, 8, 10, 12, 16, 20, 25];
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
        wall: null, clue: null,     // parsed from puzzle.grid
        ctx: null,                  // LU.makeCtx (rays / wallNeigh / whites)
        solSet: null,               // Set of solution bulb indices
        numEls: null,               // wall-number <text> elements by index
        grid: null,                 // Int8Array N*N player marks (EMPTY/BULB/XMARK)
        mode: 'cycle',
        dragging: null,
        won: false,
        hint: null, hintBanner: null,
        // Conflict display (option B): while you edit, a change can only REMOVE
        // already-shown conflicts it has resolved — it never adds. Brand-new
        // conflicts surface only after VIOLATION_DELAY_MS of no edits. The win
        // check runs live (rulesSatisfied), so finishing is still instant.
        displayed: { badPairs: [], overClues: [] },
        violationTimer: null,
        cs: 0, ox: 0, oy: 0,
    };
    let shell = null, board = null, undoHistory = null;

    function idx(r, c) { return r * state.N + c; }

    async function generatePuzzle(size, difficulty, seed) {
        return window.PuzzleGenerators.lightup(size, difficulty, seed, null);
    }

    function parsePuzzle(p) {
        const N = p.size;
        const wall = new Uint8Array(N * N);
        const clue = new Int8Array(N * N).fill(-1);
        for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
            const v = p.grid[r][c], i = r * N + c;
            if (v !== -2) { wall[i] = 1; if (v >= 0) clue[i] = v; }
        }
        state.N = N; state.wall = wall; state.clue = clue;
        state.ctx = LU.makeCtx(N, wall);
        state.solSet = new Set(p.solution.map(([r, c]) => r * N + c));
    }

    // -----------------------------------------------------------------
    // Lighting / rule helpers (operate on state.grid bulbs)
    // -----------------------------------------------------------------
    function computeLit() {
        const { N, ctx, grid } = state;
        const lit = new Uint8Array(N * N);
        for (const i of ctx.whites) if (grid[i] === BULB) { lit[i] = 1; for (const j of ctx.rays[i]) lit[j] = 1; }
        return lit;
    }
    function bulbSeesBulb(i) {
        for (const j of state.ctx.rays[i]) if (state.grid[j] === BULB) return true;
        return false;
    }
    function rulesSatisfied() {
        const { N, ctx, clue, grid } = state;
        for (const i of ctx.whites) if (grid[i] === BULB && bulbSeesBulb(i)) return false;
        for (let w = 0; w < N * N; w++) {
            if (clue[w] < 0) continue;
            let nb = 0; for (const j of ctx.wallNeigh[w]) if (grid[j] === BULB) nb++;
            if (nb !== clue[w]) return false;
        }
        const lit = computeLit();
        for (const i of ctx.whites) if (!lit[i]) return false;
        return true;
    }

    // -----------------------------------------------------------------
    // Conflict display — option B. Two errors can show red: two guards that see
    // each other, and a numbered pillar with too many adjacent guards. The win
    // check runs live (rulesSatisfied). An edit can only REMOVE shown conflicts
    // it has resolved; brand-new conflicts surface only after VIOLATION_DELAY_MS
    // of no edits — so a burst of taps/drags never flashes transient reds.
    // -----------------------------------------------------------------
    function computeViolations() {
        const { N, ctx, clue, grid } = state;
        const badPairs = [];
        for (const i of ctx.whites) {
            if (grid[i] !== BULB) continue;
            for (const j of ctx.rays[i]) if (j > i && grid[j] === BULB) badPairs.push([i, j]);
        }
        const overClues = [];
        for (let w = 0; w < N * N; w++) {
            if (clue[w] < 0) continue;
            let nb = 0; for (const j of ctx.wallNeigh[w]) if (grid[j] === BULB) nb++;
            if (nb > clue[w]) overClues.push(w);
        }
        return { badPairs, overClues };
    }
    const pairKey = (i, j) => i + '-' + j;
    function cancelViolationTimer() { if (state.violationTimer) { clearTimeout(state.violationTimer); state.violationTimer = null; } }
    function violationCount() { return state.displayed.badPairs.length + state.displayed.overClues.length; }
    function updateViolationPill() { if (shell && shell.setViolationCount) shell.setViolationCount(violationCount()); }
    function setDisplayedFull(v) { state.displayed = { badPairs: v.badPairs.slice(), overClues: v.overClues.slice() }; }
    function commitViolations() {
        state.violationTimer = null;
        setDisplayedFull(computeViolations());
        repaint(); updateStatusRow();
    }
    // An edit prunes resolved conflicts from the shown set (never adds), then
    // (re)arms the timer that reveals the full set once editing pauses.
    function refreshViolationsOnEdit() {
        const t = computeViolations();
        const badKeys = new Set(t.badPairs.map(([i, j]) => pairKey(i, j)));
        const overKeys = new Set(t.overClues);
        state.displayed.badPairs = state.displayed.badPairs.filter(([i, j]) => badKeys.has(pairKey(i, j)));
        state.displayed.overClues = state.displayed.overClues.filter((w) => overKeys.has(w));
        cancelViolationTimer();
        state.violationTimer = setTimeout(commitViolations, VIOLATION_DELAY_MS);
    }
    function showAllViolationsNow() { cancelViolationTimer(); setDisplayedFull(computeViolations()); }
    function clearViolations() { cancelViolationTimer(); state.displayed = { badPairs: [], overClues: [] }; }

    // -----------------------------------------------------------------
    // Render
    // -----------------------------------------------------------------
    function computeLayout() {
        state.cs = BOARD / state.N; state.ox = 0; state.oy = 0;
    }

    function renderBoard() {
        computeLayout();
        const { N, wall, clue, cs } = state;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        // Cell backgrounds: white board + dark walls.
        svg.appendChild(PC.svgEl('rect', { class: 'lu-cell', x: 0, y: 0, width: BOARD, height: BOARD }));
        const wg = PC.svgEl('g', { class: 'lu-walls' });
        for (let i = 0; i < N * N; i++) {
            if (!wall[i]) continue;
            const r = (i / N) | 0, c = i % N;
            wg.appendChild(PC.svgEl('rect', { class: 'lu-wall', x: c * cs, y: r * cs, width: cs, height: cs }));
        }
        svg.appendChild(wg);

        // Lit glow + reveal + symbols layers (repainted live).
        const lit = PC.svgEl('g'); lit.setAttribute('id', 'lu-lit'); svg.appendChild(lit);
        const reveal = PC.svgEl('g'); reveal.setAttribute('id', 'lu-reveal'); svg.appendChild(reveal);

        // Grid lines (thin inner, thick outer frame).
        const lines = PC.svgEl('g');
        for (let i = 0; i <= N; i++) {
            const heavy = (i === 0 || i === N);
            const clsL = 'lu-grid-line' + (heavy ? ' heavy' : '');
            lines.appendChild(PC.svgEl('line', { class: clsL, x1: i * cs, y1: 0, x2: i * cs, y2: N * cs }));
            lines.appendChild(PC.svgEl('line', { class: clsL, x1: 0, y1: i * cs, x2: N * cs, y2: i * cs }));
        }
        svg.appendChild(lines);

        // Wall numbers (static position; `.over` toggled live).
        state.numEls = {};
        const ng = PC.svgEl('g', { class: 'lu-nums' });
        const font = Math.max(10, Math.round(cs * 0.5));
        for (let i = 0; i < N * N; i++) {
            if (!wall[i] || clue[i] < 0) continue;
            const r = (i / N) | 0, c = i % N;
            const t = PC.svgEl('text', {
                class: 'lu-wall-num', x: c * cs + cs / 2, y: r * cs + cs / 2,
                'text-anchor': 'middle', 'dominant-baseline': 'middle', dy: '0.08em', 'font-size': font,
            });
            t.textContent = String(clue[i]);
            ng.appendChild(t); state.numEls[i] = t;
        }
        svg.appendChild(ng);

        const sym = PC.svgEl('g'); sym.setAttribute('id', 'lu-symbols'); svg.appendChild(sym);
        const hint = PC.svgEl('g'); hint.setAttribute('id', 'lu-hint'); svg.appendChild(hint);

        // Hit targets — white cells only.
        const hit = PC.svgEl('g', { class: 'hit' });
        for (let i = 0; i < N * N; i++) {
            if (wall[i]) continue;
            const r = (i / N) | 0, c = i % N;
            hit.appendChild(PC.svgEl('rect', { class: 'cell-hover', x: c * cs, y: r * cs, width: cs, height: cs, 'data-r': r, 'data-c': c }));
        }
        svg.appendChild(hit);

        repaint();
    }

    function repaint() {
        const { N, ctx, grid, cs, numEls, won } = state;
        const litLayer = board.querySelector('#lu-lit');
        const symLayer = board.querySelector('#lu-symbols');
        if (!litLayer || !symLayer) return;
        while (litLayer.firstChild) litLayer.removeChild(litLayer.firstChild);
        while (symLayer.firstChild) symLayer.removeChild(symLayer.firstChild);

        const dispBad = new Set(), dispOver = new Set();
        for (const [i, j] of state.displayed.badPairs) { dispBad.add(i); dispBad.add(j); }
        for (const w of state.displayed.overClues) dispOver.add(w);

        const lit = computeLit();
        for (const i of ctx.whites) {
            if (!lit[i]) continue;
            const r = (i / N) | 0, c = i % N;
            litLayer.appendChild(PC.svgEl('rect', { class: 'lu-lit' + (won ? ' won' : ''), x: c * cs, y: r * cs, width: cs, height: cs }));
        }

        // Wall-number over-satisfied colouring (from the debounced display set).
        if (numEls) for (const k in numEls) {
            const w = +k;
            numEls[w].classList.toggle('over', !won && dispOver.has(w));
        }

        // Bulbs + ✗.
        const bulbSize = cs * 0.66;
        for (const i of ctx.whites) {
            const r = (i / N) | 0, c = i % N;
            const cx = c * cs + cs / 2, cy = r * cs + cs / 2;
            if (grid[i] === BULB) {
                const bad = !won && dispBad.has(i);
                const g = PC.boardIcon(EMITTER_ICON, cx, cy, bulbSize, { className: 'lu-bulb' + (bad ? ' bad' : '') + (won ? ' won' : '') });
                if (g) symLayer.appendChild(g);
            } else if (grid[i] === XMARK && !won) {
                const m = cs * 0.3, sw = Math.max(1.4, cs * 0.06), x0 = c * cs, y0 = r * cs;
                symLayer.appendChild(PC.svgEl('line', { class: 'lu-x', 'stroke-width': sw, x1: x0 + m, y1: y0 + m, x2: x0 + cs - m, y2: y0 + cs - m }));
                symLayer.appendChild(PC.svgEl('line', { class: 'lu-x', 'stroke-width': sw, x1: x0 + cs - m, y1: y0 + m, x2: x0 + m, y2: y0 + cs - m }));
            }
        }
    }

    // -----------------------------------------------------------------
    // Interaction
    // -----------------------------------------------------------------
    function eventToCell(ev) {
        if (!state.puzzle) return null;
        const rect = board.getBoundingClientRect();
        if (!rect.width || !rect.height) return null;
        const vbx = (ev.clientX - rect.left) / rect.width * 486 - 3;
        const vby = (ev.clientY - rect.top) / rect.height * 486 - 3;
        if (vbx < 0 || vby < 0) return null;
        const c = Math.floor(vbx / state.cs), r = Math.floor(vby / state.cs);
        if (r < 0 || r >= state.N || c < 0 || c >= state.N) return null;
        if (state.wall[idx(r, c)]) return null; // walls aren't interactive
        return [r, c];
    }

    function onPointerDown(ev) {
        if (!state.puzzle || state.won) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        const cell = eventToCell(ev); if (!cell) return;
        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        clearHint();
        pushUndo();
        const [r, c] = cell;
        const target = resolveTarget(state.mode, state.grid[idx(r, c)]);
        state.dragging = { pointerId: ev.pointerId, target, last: [r, c] };
        if (state.grid[idx(r, c)] !== target) { state.grid[idx(r, c)] = target; afterChange(); }
    }

    function onPointerMove(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        const cell = eventToCell(ev); if (!cell) return;
        const [r, c] = cell;
        if (d.last[0] === r && d.last[1] === c) return;
        d.last = [r, c];
        if (state.grid[idx(r, c)] !== d.target) { state.grid[idx(r, c)] = d.target; afterChange(); }
    }

    function onPointerEnd(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        try { board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        state.dragging = null;
    }

    function setMode(mode) {
        if (!VALID_MODES.includes(mode)) return;
        state.mode = mode;
        document.querySelectorAll('#lu-tools .lu-tool').forEach((b) => {
            const on = b.dataset.mode === mode;
            b.classList.toggle('active', on);
            b.setAttribute('aria-checked', on ? 'true' : 'false');
        });
    }

    function afterChange() {
        refreshViolationsOnEdit();
        repaint();
        if (!state.won && rulesSatisfied()) {
            state.won = true;
            shell.markSolved();
            clearViolations();
            if (state.dragging) { try { board.releasePointerCapture(state.dragging.pointerId); } catch (_) { /* ignore */ } state.dragging = null; }
            clearHint();
            const rl = board.querySelector('#lu-reveal'); if (rl) while (rl.firstChild) rl.removeChild(rl.firstChild);
            repaint();
        }
        updateStatusRow();
        updateUndoButton();
    }

    function updateStatusRow() { shell.setWin(state.won); updateViolationPill(); }

    // -----------------------------------------------------------------
    // Undo
    // -----------------------------------------------------------------
    function snapshotState() { return { grid: state.grid.slice() }; }
    function restoreSnapshot(snap) {
        const wasWon = state.won;
        state.grid = snap.grid.slice();
        state.dragging = null; state.won = false;
        if (wasWon) shell.clearWin();
        showAllViolationsNow();
        clearHint(); repaint(); updateStatusRow();
    }
    function pushUndo() { if (undoHistory && !state.won) { undoHistory.push(); updateUndoButton(); } }
    function doUndo() { if (state.puzzle && undoHistory && undoHistory.undo()) updateUndoButton(); }
    function updateUndoButton() { const btn = document.getElementById('undo-btn'); if (btn) btn.disabled = !(undoHistory && undoHistory.canUndo()); }

    // -----------------------------------------------------------------
    // Hints — wrong marks first, else the next basic deduction.
    // -----------------------------------------------------------------
    const XI = '<span class="inline-icon lu-ico-mark" data-icon="x"></span>'; // the ✗ mark as an icon
    const HINT_TEXTS = {
        en: {
            wrong: 'The highlighted cell(s) disagree with the solution — a guard that shouldn’t be there, or a ' + XI + ' where a guard belongs.',
            conflict: (h) => h.sight && h.over
                ? 'The highlighted cells break a rule — two guards can see each other, and a numbered pillar has too many guards beside it.'
                : h.sight
                    ? 'The highlighted guards can see each other — no two guards may.'
                    : 'This numbered pillar has too many guards beside it — it must hold exactly its number.',
            clueBulb: (n) => `A numbered pillar forces it: the ${n} highlighted cell(s) must hold a guard.`,
            clueNo: (n) => `A numbered pillar is already satisfied — the ${n} highlighted cell(s) can’t hold a guard (${XI}).`,
            cover: () => 'Only a guard here can watch the highlighted dark cell.',
            none: 'Nothing more to deduce right now.',
        },
        zh: {
            wrong: '醒目格與唯一解不符——有不該放的守衛，或在該放守衛的格打了 ' + XI + '。',
            conflict: (h) => h.sight && h.over
                ? '醒目的格子違反了規則——有兩名守衛互相看到，且有數字柱旁的守衛過多。'
                : h.sight
                    ? '醒目的兩名守衛互相看到了——任兩名守衛都不能看到對方。'
                    : '醒目的數字柱旁守衛太多了——數量必須剛好等於柱上的數字。',
            clueBulb: (n) => `數字柱逼出：醒目的 ${n} 格必須放守衛。`,
            clueNo: (n) => `數字柱已滿足：醒目的 ${n} 格不能放守衛（${XI}）。`,
            cover: () => '只有在這格放守衛，才能照亮醒目的暗格。',
            none: '目前沒有可推的下一步。',
        },
    };
    function hintTexts() { const l = (PC.i18n && PC.i18n.locale) || 'en'; return HINT_TEXTS[l] || HINT_TEXTS.en; }

    function computeHint() {
        const { ctx, clue, grid, solSet } = state;
        // 1) A live rule break comes first — warn about the broken rule itself
        //    rather than comparing against the solution.
        const v = computeViolations();
        if (v.badPairs.length || v.overClues.length) {
            const cells = new Set();
            for (const [i, j] of v.badPairs) { cells.add(i); cells.add(j); }
            for (const w of v.overClues) cells.add(w);
            return { kind: 'conflict', cells: [...cells], sight: v.badPairs.length > 0, over: v.overClues.length > 0 };
        }
        // 2) Otherwise, cells that disagree with the unique solution.
        const wrong = [];
        for (const i of ctx.whites) {
            if (grid[i] === BULB && !solSet.has(i)) wrong.push(i);
            else if (grid[i] === XMARK && solSet.has(i)) wrong.push(i);
        }
        if (wrong.length) return { kind: 'wrong', cells: wrong };
        // Treat every cell already in a placed guard's sight as a virtual ✗, so
        // the hint never nags you to mark "already-watched" cells — it surfaces
        // guards to place and only genuine (non-shadow) exclusions.
        const aug = grid.slice();
        for (const i of ctx.whites) if (aug[i] === BULB) for (const j of ctx.rays[i]) if (aug[j] === EMPTY) aug[j] = XMARK;
        const step = LU.nextStep(ctx, clue, aug);
        if (step) return { kind: 'deduce', cells: step.cells, state: step.state, reason: step.reason, anchor: step.anchor };
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
        else if (h.reason === 'cover') html = t.cover();
        else html = (h.state === BULB) ? t.clueBulb(h.cells.length) : t.clueNo(h.cells.length);
        state.hintBanner.innerHTML = html;
        if (PC.icons && PC.icons.render) PC.icons.render(state.hintBanner);
        state.hintBanner.classList.toggle('error', h.kind === 'wrong' || h.kind === 'conflict');
        state.hintBanner.hidden = false;
    }
    function repaintHint() {
        const layer = board && board.querySelector('#lu-hint');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const h = state.hint; if (!h || h.kind === 'none') return;
        const { N, cs } = state;
        const ring = (i, wrong) => {
            const r = (i / N) | 0, c = i % N;
            layer.appendChild(PC.svgEl('rect', {
                class: 'lu-hint-ring' + (wrong ? ' wrong' : ''), x: c * cs + cs * 0.08, y: r * cs + cs * 0.08,
                width: cs * 0.84, height: cs * 0.84, rx: cs * 0.14, ry: cs * 0.14,
            }));
        };
        const ghost = (i) => {
            const r = (i / N) | 0, c = i % N, cx = c * cs + cs / 2, cy = r * cs + cs / 2;
            if (h.state === BULB) {
                const g = PC.boardIcon(EMITTER_ICON, cx, cy, cs * 0.6, { className: 'lu-bulb lu-hint-ghost' });
                if (g) layer.appendChild(g);
            } else {
                const m = cs * 0.32, sw = Math.max(1.4, cs * 0.06), x0 = c * cs, y0 = r * cs;
                layer.appendChild(PC.svgEl('line', { class: 'lu-x lu-hint-ghost', 'stroke-width': sw, x1: x0 + m, y1: y0 + m, x2: x0 + cs - m, y2: y0 + cs - m }));
                layer.appendChild(PC.svgEl('line', { class: 'lu-x lu-hint-ghost', 'stroke-width': sw, x1: x0 + cs - m, y1: y0 + m, x2: x0 + m, y2: y0 + cs - m }));
            }
        };
        if (h.kind === 'wrong' || h.kind === 'conflict') { for (const i of h.cells) ring(i, true); return; }
        // deduce: outline the source (numbered pillar, or for coverage the dark
        // cell being rescued) — unless it coincides with a highlighted cell.
        if (h.anchor >= 0 && h.cells.indexOf(h.anchor) === -1) {
            const ar = (h.anchor / N) | 0, ac = h.anchor % N;
            layer.appendChild(PC.svgEl('rect', {
                class: 'lu-hint-anchor', x: ac * cs + cs * 0.06, y: ar * cs + cs * 0.06,
                width: cs * 0.88, height: cs * 0.88, rx: cs * 0.1, ry: cs * 0.1,
            }));
        }
        for (const i of h.cells) { ghost(i); ring(i, false); }
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
        state.grid = new Int8Array(state.N * state.N);
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
        state.grid = new Int8Array(state.N * state.N);
        state.won = false; clearViolations(); clearHint(); repaint(); updateStatusRow(); updateUndoButton();
    }
    function onReveal() {
        const layer = board && board.querySelector('#lu-reveal');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        if (shell.revealed && !state.won) {
            const { N, cs } = state;
            for (const i of state.solSet) {
                const r = (i / N) | 0, c = i % N;
                const g = PC.boardIcon(EMITTER_ICON, c * cs + cs / 2, r * cs + cs / 2, cs * 0.6, { className: 'lu-reveal' });
                if (g) layer.appendChild(g);
            }
        }
        repaintHint();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------
    function init() {
        shell = PC.shell.create({
            gameId: 'lightup',
            difficulty: { default: urlInitial ? urlInitial.difficulty : 'medium' },
            size: { kind: 'slider', values: SIZE_STEPS, min: MIN_SIZE, max: MAX_SIZE, default: urlInitial ? urlInitial.size : 10 },
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

        const tools = document.getElementById('lu-tools');
        if (tools) tools.addEventListener('click', (ev) => { const btn = ev.target.closest('.lu-tool'); if (btn && btn.dataset.mode) setMode(btn.dataset.mode); });
        setMode('cycle');

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
            if ((ev.ctrlKey || ev.metaKey) && !ev.shiftKey && !ev.altKey && (ev.key === 'z' || ev.key === 'Z')) { doUndo(); ev.preventDefault(); return; }
            if (ev.ctrlKey || ev.metaKey || ev.altKey) return;
            const k = ev.key.toLowerCase();
            const mode = (k === '1') ? 'cycle' : (k === '2' || k === 'b') ? 'bulb' : (k === '3' || k === 'x') ? 'block' : (k === '4' || k === 'e') ? 'empty' : null;
            if (mode) { setMode(mode); ev.preventDefault(); }
        });

        shell.start();
    }

    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
})();
