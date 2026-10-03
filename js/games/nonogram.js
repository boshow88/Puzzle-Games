/**
 * Nonogram (Picross) — game UI.
 *
 * Consumes window.PuzzleGenerators.nonogram and the shared shell. Cells cycle
 * empty → filled → ✗(blocked) → empty on tap, and a drag paints the first
 * cell's new state. Win when the filled cells match the unique solution.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;
    const Solver = window.PuzzleSolvers.nonogram;
    const BOARD = 486;

    const EMPTY = 0, FILL = 1, BLOCK = 2;

    // -----------------------------------------------------------------
    // Shareable URL (size/diff/seed), mirroring the other games.
    // -----------------------------------------------------------------
    const MIN_SIZE = 5, MAX_SIZE = 12;
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
        grid: null,             // Int8Array N*N: 0 empty, 1 filled, 2 blocked
        dragging: null,         // { pointerId, mode, last:[r,c] }
        won: false,
        hint: null,
        hintBanner: null,
        // layout (recomputed per puzzle)
        cs: 0, ox: 0, oy: 0, gutter: 0,
    };
    let shell = null;
    let board = null;
    let undoHistory = null;

    async function generatePuzzle(size, difficulty, seed) {
        // Generation is sub-50ms, so skip the determinate bar and let the
        // shell's indeterminate overlay flash briefly.
        return window.PuzzleGenerators.nonogram(size, difficulty, seed, null);
    }

    // -----------------------------------------------------------------
    // Layout — equal top/left gutters sized to the longest clue so the
    // square grid fills the rest of the 486×486 box.
    // -----------------------------------------------------------------
    function computeLayout() {
        const p = state.puzzle, N = p.size;
        let maxR = 1, maxC = 1;
        for (const cl of p.rowClues) maxR = Math.max(maxR, cl.length || 1);
        for (const cl of p.colClues) maxC = Math.max(maxC, cl.length || 1);
        const gutter = Math.max(maxR, maxC, 1);
        const cs = BOARD / (N + gutter);
        state.cs = cs; state.gutter = gutter; state.ox = gutter * cs; state.oy = gutter * cs;
    }

    function idx(r, c) { return r * state.puzzle.size + c; }

    // -----------------------------------------------------------------
    // Render
    // -----------------------------------------------------------------
    function renderBoard() {
        computeLayout();
        const p = state.puzzle, N = p.size, { cs, ox, oy } = state;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        // Grid cell backgrounds.
        const bg = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                bg.appendChild(PC.svgEl('rect', {
                    class: 'nono-cell-bg', x: ox + c * cs, y: oy + r * cs, width: cs, height: cs,
                }));
            }
        }
        svg.appendChild(bg);

        // Grid lines (every 5th heavier, nonogram convention).
        const lines = PC.svgEl('g', { class: 'nono-grid' });
        for (let i = 0; i <= N; i++) {
            const heavy = (i % 5 === 0) || i === N;
            const cls = 'nono-grid-line' + (heavy ? ' heavy' : '');
            lines.appendChild(PC.svgEl('line', { class: cls, x1: ox + i * cs, y1: oy, x2: ox + i * cs, y2: oy + N * cs }));
            lines.appendChild(PC.svgEl('line', { class: cls, x1: ox, y1: oy + i * cs, x2: ox + N * cs, y2: oy + i * cs }));
        }
        svg.appendChild(lines);

        // Clue numbers.
        const clueG = PC.svgEl('g', { class: 'nono-clues' });
        const font = Math.max(10, Math.floor(cs * 0.5));
        for (let r = 0; r < N; r++) {
            const cl = p.rowClues[r].length ? p.rowClues[r] : [0];
            for (let i = 0; i < cl.length; i++) {
                const t = PC.svgEl('text', {
                    class: 'nono-clue' + (p.rowClues[r].length ? '' : ' zero'),
                    x: ox - (cl.length - i - 0.5) * cs, y: oy + r * cs + cs / 2,
                    'text-anchor': 'middle', 'dominant-baseline': 'middle', dy: '0.08em', 'font-size': font,
                });
                t.textContent = String(cl[i]);
                clueG.appendChild(t);
            }
        }
        for (let c = 0; c < N; c++) {
            const cl = p.colClues[c].length ? p.colClues[c] : [0];
            for (let i = 0; i < cl.length; i++) {
                const t = PC.svgEl('text', {
                    class: 'nono-clue' + (p.colClues[c].length ? '' : ' zero'),
                    x: ox + c * cs + cs / 2, y: oy - (cl.length - i - 0.5) * cs,
                    'text-anchor': 'middle', 'dominant-baseline': 'middle', dy: '0.08em', 'font-size': font,
                });
                t.textContent = String(cl[i]);
                clueG.appendChild(t);
            }
        }
        svg.appendChild(clueG);

        // Symbols (filled / ✗) — rebuilt by repaintCells.
        const sym = PC.svgEl('g', { class: 'nono-symbols' });
        sym.setAttribute('id', 'nono-symbols');
        svg.appendChild(sym);

        // Hint overlay.
        const hint = PC.svgEl('g', { class: 'nono-hint' });
        hint.setAttribute('id', 'nono-hint');
        svg.appendChild(hint);

        // Hit targets.
        const hit = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                hit.appendChild(PC.svgEl('rect', {
                    class: 'cell-hover', x: ox + c * cs, y: oy + r * cs, width: cs, height: cs,
                    'data-r': r, 'data-c': c,
                }));
            }
        }
        svg.appendChild(hit);

        repaintCells();
    }

    function repaintCells() {
        const layer = board.querySelector('#nono-symbols');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const p = state.puzzle, N = p.size, { cs, ox, oy } = state;
        const inset = Math.max(1, cs * 0.06);
        const won = state.won;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = state.grid[idx(r, c)];
                if (v === FILL) {
                    layer.appendChild(PC.svgEl('rect', {
                        class: 'nono-fill' + (won ? ' won' : ''),
                        x: ox + c * cs + inset, y: oy + r * cs + inset,
                        width: cs - inset * 2, height: cs - inset * 2,
                        rx: Math.max(1, cs * 0.08), ry: Math.max(1, cs * 0.08),
                    }));
                } else if (v === BLOCK && !won) {
                    const m = cs * 0.28;
                    const x0 = ox + c * cs, y0 = oy + r * cs;
                    layer.appendChild(PC.svgEl('line', { class: 'nono-x', x1: x0 + m, y1: y0 + m, x2: x0 + cs - m, y2: y0 + cs - m }));
                    layer.appendChild(PC.svgEl('line', { class: 'nono-x', x1: x0 + cs - m, y1: y0 + m, x2: x0 + m, y2: y0 + cs - m }));
                }
            }
        }
    }

    // -----------------------------------------------------------------
    // Interaction
    // -----------------------------------------------------------------
    function eventToCell(ev) {
        const p = state.puzzle; if (!p) return null;
        const rect = board.getBoundingClientRect();
        if (!rect.width || !rect.height) return null;
        const x = (ev.clientX - rect.left) / rect.width * BOARD - state.ox;
        const y = (ev.clientY - rect.top) / rect.height * BOARD - state.oy;
        if (x < 0 || y < 0) return null;
        const c = Math.floor(x / state.cs), r = Math.floor(y / state.cs);
        if (r < 0 || r >= p.size || c < 0 || c >= p.size) return null;
        return [r, c];
    }

    function cycle(v) { return v === EMPTY ? FILL : v === FILL ? BLOCK : EMPTY; }

    function onPointerDown(ev) {
        if (!state.puzzle || state.won) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        const cell = eventToCell(ev); if (!cell) return;
        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        clearHint();
        pushUndo();
        const [r, c] = cell;
        const next = cycle(state.grid[idx(r, c)]);
        state.grid[idx(r, c)] = next;
        state.dragging = { pointerId: ev.pointerId, mode: next, last: [r, c] };
        afterChange();
    }

    function onPointerMove(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        const cell = eventToCell(ev); if (!cell) return;
        const [r, c] = cell;
        if (d.last[0] === r && d.last[1] === c) return;
        d.last = [r, c];
        if (state.grid[idx(r, c)] !== d.mode) {
            state.grid[idx(r, c)] = d.mode;
            afterChange();
        }
    }

    function onPointerEnd(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        try { board.releasePointerCapture(ev.pointerId); } catch (_) { /* ignore */ }
        state.dragging = null;
    }

    function afterChange() {
        repaintCells();
        if (!state.won && isWin()) {
            state.won = true;
            shell.markSolved();
            if (state.dragging) {
                try { board.releasePointerCapture(state.dragging.pointerId); } catch (_) { /* ignore */ }
                state.dragging = null;
            }
            clearHint();
            repaintCells();
        }
        updateStatusRow();
        updateUndoButton();
    }

    function isWin() {
        const p = state.puzzle, N = p.size;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const filled = state.grid[idx(r, c)] === FILL;
                if (filled !== (p.solution[r][c] === 1)) return false;
            }
        }
        return true;
    }

    function updateStatusRow() { shell.setWin(state.won); }

    // -----------------------------------------------------------------
    // Undo (one gesture = one step)
    // -----------------------------------------------------------------
    function snapshotState() { return { grid: state.grid.slice() }; }
    function restoreSnapshot(snap) {
        const wasWon = state.won;
        state.grid = snap.grid.slice();
        state.dragging = null;
        state.won = false;
        if (wasWon) shell.clearWin();
        clearHint();
        repaintCells();
        updateStatusRow();
    }
    function pushUndo() { if (undoHistory && !state.won) { undoHistory.push(); updateUndoButton(); } }
    function doUndo() { if (state.puzzle && undoHistory && undoHistory.undo()) updateUndoButton(); }
    function updateUndoButton() {
        const btn = document.getElementById('undo-btn');
        if (btn) btn.disabled = !(undoHistory && undoHistory.canUndo());
    }

    // -----------------------------------------------------------------
    // Hints — wrong cell(s) first, else the next forced line deduction.
    // -----------------------------------------------------------------
    const HINT_UI_TEXTS = {
        en: {
            wrong: 'The highlighted cell(s) don’t match the unique solution — a filled cell must be blank, or a blanked cell must be filled.',
            row: (n, clue) => `Row ${n}: the clue ${clue} forces the highlighted cell(s).`,
            col: (n, clue) => `Column ${n}: the clue ${clue} forces the highlighted cell(s).`,
            none: 'Nothing more can be deduced by single-line logic right now.',
        },
        zh: {
            wrong: '醒目標示的格子與唯一解不符——有該留空的格被填了,或該填的格被劃掉了。',
            row: (n, clue) => `第 ${n} 列:線索 ${clue} 可推出醒目標示的格子。`,
            col: (n, clue) => `第 ${n} 行:線索 ${clue} 可推出醒目標示的格子。`,
            none: '目前用單行邏輯已無法再推出新格子。',
        },
    };
    function hintTexts() { const l = (PC.i18n && PC.i18n.locale) || 'en'; return HINT_UI_TEXTS[l] || HINT_UI_TEXTS.en; }

    function computeHint() {
        const p = state.puzzle, N = p.size;
        const wrong = [];
        for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
            const v = state.grid[idx(r, c)], sol = p.solution[r][c];
            if ((v === FILL && sol === 0) || (v === BLOCK && sol === 1)) wrong.push([r, c]);
        }
        if (wrong.length) return { kind: 'wrong', cells: wrong };
        const step = Solver.nextStep(p.rowClues, p.colClues, N, state.grid);
        if (step) return { kind: 'deduce', orient: step.orient, index: step.index, clue: step.clue, cells: step.cells.map((x) => [x.r, x.c]) };
        return null;
    }

    function showHint() {
        if (!state.puzzle || state.won) return;
        if (state.hint) { clearHint(); return; }
        const h = computeHint();
        if (!h) { state.hint = { kind: 'none' }; renderHintBanner(); return; }
        state.hint = h;
        renderHintBanner();
        repaintHint();
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
        let text;
        if (h.kind === 'wrong') text = t.wrong;
        else if (h.kind === 'none') text = t.none;
        else text = (h.orient === 'row' ? t.row : t.col)(h.index + 1, '[' + h.clue.join(' ') + ']');
        state.hintBanner.textContent = text;
        state.hintBanner.classList.toggle('error', h.kind === 'wrong');
        state.hintBanner.hidden = false;
    }

    function repaintHint() {
        const layer = board && board.querySelector('#nono-hint');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const h = state.hint; if (!h || h.kind === 'none') return;
        const p = state.puzzle, N = p.size, { cs, ox, oy } = state;
        if (h.kind === 'deduce') {
            // Spotlight the target line, then ring the forced cells.
            if (h.orient === 'row') {
                layer.appendChild(PC.svgEl('rect', { class: 'nono-hint-line', x: ox, y: oy + h.index * cs, width: N * cs, height: cs }));
            } else {
                layer.appendChild(PC.svgEl('rect', { class: 'nono-hint-line', x: ox + h.index * cs, y: oy, width: cs, height: N * cs }));
            }
        }
        const cls = h.kind === 'wrong' ? 'nono-hint-ring wrong' : 'nono-hint-ring';
        for (const [r, c] of h.cells) {
            layer.appendChild(PC.svgEl('rect', {
                class: cls, x: ox + c * cs + cs * 0.1, y: oy + r * cs + cs * 0.1,
                width: cs * 0.8, height: cs * 0.8, rx: cs * 0.12, ry: cs * 0.12,
            }));
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
        state.grid = new Int8Array(shell.size * shell.size);
        state.dragging = null;
        state.won = false;
        state.hint = null;
        if (undoHistory) undoHistory.clear();
        renderBoard();
        updateStatusRow();
        updateUndoButton();
        if (PC.share) PC.share.replaceUrl({ size: shell.size, difficulty: shell.difficulty, seed });
    }

    function resetBoard() {
        if (!state.puzzle) return;
        if (state.won) { if (undoHistory) undoHistory.clear(); }
        else pushUndo();
        state.grid = new Int8Array(state.puzzle.size * state.puzzle.size);
        state.won = false;
        clearHint();
        repaintCells();
        updateStatusRow();
        updateUndoButton();
    }

    function onReveal() {
        clearHint();
        // Reveal overlay: show the solution's filled cells faintly.
        const layer = board && board.querySelector('#nono-hint');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        if (!shell.revealed || state.won) return;
        const p = state.puzzle, N = p.size, { cs, ox, oy } = state;
        for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
            if (p.solution[r][c] === 1) {
                layer.appendChild(PC.svgEl('rect', {
                    class: 'nono-reveal', x: ox + c * cs + cs * 0.18, y: oy + r * cs + cs * 0.18,
                    width: cs * 0.64, height: cs * 0.64, rx: cs * 0.1, ry: cs * 0.1,
                }));
            }
        }
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------
    function init() {
        shell = PC.shell.create({
            gameId: 'nonogram',
            difficulty: { default: urlInitial ? urlInitial.difficulty : 'medium' },
            size: { kind: 'slider', min: MIN_SIZE, max: MAX_SIZE, default: urlInitial ? urlInitial.size : 10 },
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

        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerEnd);
        board.addEventListener('pointercancel', onPointerEnd);
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());

        if (PC.i18n && typeof PC.i18n.subscribe === 'function') {
            PC.i18n.subscribe(() => { if (state.hint) renderHintBanner(); });
        }
        window.addEventListener('keydown', (ev) => {
            if ((ev.ctrlKey || ev.metaKey) && !ev.shiftKey && !ev.altKey && (ev.key === 'z' || ev.key === 'Z')) {
                doUndo(); ev.preventDefault();
            }
        });

        shell.start();
    }

    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
})();
