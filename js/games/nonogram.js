/**
 * Nonogram (Picross) — game UI.
 *
 * Consumes window.PuzzleGenerators.nonogram and the shared shell. An input-mode
 * selector (Cycle / Fill / Mark / Erase) decides how a tap changes a cell; a
 * drag paints the content decided by its start cell (add vs remove), à la
 * Queens. Win when the filled cells match the unique solution.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;
    const Solver = window.PuzzleSolvers.nonogram;
    // Board drawing area is 480; the SVG viewBox is "-3 -3 486 486" (matching
    // every other game) so the stroke-3 outer frame gets 3px of bleed instead
    // of being clipped in half at the edges.
    const BOARD = 480;

    const EMPTY = 0, FILL = 1, BLOCK = 2;
    // Input modes, Queens-style: tapping a cell cycles/toggles its state, and a
    // drag paints the content decided by its START cell (add vs remove). The
    // four modes give a cell 3 / 2 / 2 / 1 reachable states respectively.
    const VALID_MODES = ['cycle', 'fill', 'block', 'empty'];
    function resolveTarget(mode, cur) {
        if (mode === 'cycle') return cur === EMPTY ? FILL : cur === FILL ? BLOCK : EMPTY;
        if (mode === 'fill') return cur === FILL ? EMPTY : FILL;
        if (mode === 'block') return cur === BLOCK ? EMPTY : BLOCK;
        return EMPTY; // 'empty' = erase
    }

    // -----------------------------------------------------------------
    // Shareable URL (size/diff/seed), mirroring the other games.
    // -----------------------------------------------------------------
    const MIN_SIZE = 6, MAX_SIZE = 16;
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
        mode: 'cycle',          // active input mode: 'cycle' | 'fill' | 'block' | 'empty'
        dragging: null,         // { pointerId, target, last:[r,c] }
        won: false,
        hint: null,
        hintBanner: null,
        // layout (recomputed per puzzle)
        cs: 0, ox: 0, oy: 0, gutter: 0, clueSlot: 0,
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
    const CLUE_SLOT_FRAC = 0.66; // clue numbers sit in slots narrower than a cell

    function computeLayout() {
        const N = state.puzzle.size;
        // Reserve the gutter for the THEORETICAL max clue count for this N
        // (⌈N/2⌉ — the most runs a line can hold), not the current puzzle's
        // longest clue, so cells are the same size for every board of a size.
        // Numbers are packed into narrow slots so the gutter stays compact.
        const gutter = Math.ceil(N / 2);
        const cs = BOARD / (N + gutter * CLUE_SLOT_FRAC);
        const slot = cs * CLUE_SLOT_FRAC;
        state.cs = cs; state.gutter = gutter; state.clueSlot = slot;
        state.ox = gutter * slot; state.oy = gutter * slot;
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

        // White background behind the main grid only (clue gutter stays clear).
        svg.appendChild(PC.svgEl('rect', { class: 'nono-cell-bg', x: ox, y: oy, width: N * cs, height: N * cs }));

        // Grid lines over the main grid only — thin inside, a thick frame on the
        // four outer edges (no every-5th heavy lines).
        const lines = PC.svgEl('g', { class: 'nono-grid' });
        for (let i = 0; i <= N; i++) {
            const heavy = (i === 0 || i === N);
            const cls = 'nono-grid-line' + (heavy ? ' heavy' : '');
            lines.appendChild(PC.svgEl('line', { class: cls, x1: ox + i * cs, y1: oy, x2: ox + i * cs, y2: oy + N * cs }));
            lines.appendChild(PC.svgEl('line', { class: cls, x1: ox, y1: oy + i * cs, x2: ox + N * cs, y2: oy + i * cs }));
        }
        svg.appendChild(lines);

        // Clue-satisfied highlight band (drawn BELOW the numbers so they stay
        // readable); repainted live by repaintClueHighlights on every change.
        const clueHl = PC.svgEl('g', { class: 'nono-clue-hl-layer' });
        clueHl.setAttribute('id', 'nono-clue-hl');
        svg.appendChild(clueHl);

        // Clue numbers — small markers, packed in narrow slots within the gutter.
        const clueG = PC.svgEl('g', { class: 'nono-clues' });
        const slot = state.clueSlot;
        const font = Math.max(9, Math.round(cs * 0.38));
        for (let r = 0; r < N; r++) {
            const cl = p.rowClues[r].length ? p.rowClues[r] : [0];
            for (let i = 0; i < cl.length; i++) {
                const t = PC.svgEl('text', {
                    class: 'nono-clue' + (p.rowClues[r].length ? '' : ' zero'),
                    x: ox - (cl.length - i - 0.5) * slot, y: oy + r * cs + cs / 2,
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
                    x: ox + c * cs + cs / 2, y: oy - (cl.length - i - 0.5) * slot,
                    'text-anchor': 'middle', 'dominant-baseline': 'middle', dy: '0.08em', 'font-size': font,
                });
                t.textContent = String(cl[i]);
                clueG.appendChild(t);
            }
        }
        svg.appendChild(clueG);

        // Reveal overlay (solution fills) — drawn BELOW the player's symbols so
        // a correctly-filled cell's opaque fill covers it (no dark two-layer
        // stack), and on its own layer so hint and reveal never wipe each other.
        const reveal = PC.svgEl('g', { class: 'nono-reveal-layer' });
        reveal.setAttribute('id', 'nono-reveal');
        svg.appendChild(reveal);

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
                    const attrs = {
                        class: 'nono-fill' + (won ? ' won' : ''),
                        x: ox + c * cs + inset, y: oy + r * cs + inset,
                        width: cs - inset * 2, height: cs - inset * 2,
                        rx: Math.max(1, cs * 0.08), ry: Math.max(1, cs * 0.08),
                    };
                    // On win, stagger the pop diagonally for a ripple effect.
                    if (won) attrs.style = 'animation-delay:' + ((r + c) * 45) + 'ms';
                    layer.appendChild(PC.svgEl('rect', attrs));
                } else if (v === BLOCK) {
                    // The player's ✗ marks stay on the board, even after winning.
                    const m = cs * 0.28;
                    const x0 = ox + c * cs, y0 = oy + r * cs;
                    layer.appendChild(PC.svgEl('line', { class: 'nono-x', x1: x0 + m, y1: y0 + m, x2: x0 + cs - m, y2: y0 + cs - m }));
                    layer.appendChild(PC.svgEl('line', { class: 'nono-x', x1: x0 + cs - m, y1: y0 + m, x2: x0 + m, y2: y0 + cs - m }));
                }
            }
        }
        repaintClueHighlights();
    }

    // True when the line's FILLED runs exactly match its clue (ignoring ✗/empty),
    // regardless of whether it agrees with the hidden solution.
    function lineSatisfied(cells, clue) {
        const runs = [];
        let run = 0;
        for (const v of cells) { if (v === FILL) run++; else if (run) { runs.push(run); run = 0; } }
        if (run) runs.push(run);
        if (runs.length !== clue.length) return false;
        for (let i = 0; i < clue.length; i++) if (runs[i] !== clue[i]) return false;
        return true;
    }

    // Highlight the clue of every row/column whose filled runs currently match it.
    function repaintClueHighlights() {
        const layer = board && board.querySelector('#nono-clue-hl');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        const p = state.puzzle; if (!p) return;
        const N = p.size, { cs, ox, oy, clueSlot: slot } = state;
        const vIn = cs * 0.12, hFrac = 0.76;
        for (let r = 0; r < N; r++) {
            const clue = p.rowClues[r];
            if (clue.length === 0) continue; // empty "0" lines: trivially done, don't mark
            const cells = [];
            for (let c = 0; c < N; c++) cells.push(state.grid[idx(r, c)]);
            if (lineSatisfied(cells, clue)) {
                layer.appendChild(PC.svgEl('rect', {
                    class: 'nono-clue-hl', x: ox - clue.length * slot, y: oy + r * cs + vIn,
                    width: clue.length * slot, height: cs * hFrac, rx: cs * 0.1, ry: cs * 0.1,
                }));
            }
        }
        for (let c = 0; c < N; c++) {
            const clue = p.colClues[c];
            if (clue.length === 0) continue; // empty "0" lines: trivially done, don't mark
            const cells = [];
            for (let r = 0; r < N; r++) cells.push(state.grid[idx(r, c)]);
            if (lineSatisfied(cells, clue)) {
                layer.appendChild(PC.svgEl('rect', {
                    class: 'nono-clue-hl', x: ox + c * cs + vIn, y: oy - clue.length * slot,
                    width: cs * hFrac, height: clue.length * slot, rx: cs * 0.1, ry: cs * 0.1,
                }));
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
        // The viewBox is "-3 -3 486 486", so the drawing area (0..480) maps to
        // the inner 480/486 of the rendered SVG, offset by 3/486 on each side.
        const vbx = (ev.clientX - rect.left) / rect.width * 486 - 3;
        const vby = (ev.clientY - rect.top) / rect.height * 486 - 3;
        const x = vbx - state.ox;
        const y = vby - state.oy;
        if (x < 0 || y < 0) return null;
        const c = Math.floor(x / state.cs), r = Math.floor(y / state.cs);
        if (r < 0 || r >= p.size || c < 0 || c >= p.size) return null;
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
        if (state.grid[idx(r, c)] !== target) {
            state.grid[idx(r, c)] = target;
            afterChange();
        }
    }

    function onPointerMove(ev) {
        const d = state.dragging;
        if (!d || ev.pointerId !== d.pointerId) return;
        const cell = eventToCell(ev); if (!cell) return;
        const [r, c] = cell;
        if (d.last[0] === r && d.last[1] === c) return;
        d.last = [r, c];
        if (state.grid[idx(r, c)] !== d.target) {
            state.grid[idx(r, c)] = d.target;
            afterChange();
        }
    }

    function setMode(mode) {
        if (!VALID_MODES.includes(mode)) return;
        state.mode = mode;
        const btns = document.querySelectorAll('#nono-tools .nono-tool');
        btns.forEach((b) => {
            const on = b.dataset.mode === mode;
            b.classList.toggle('active', on);
            b.setAttribute('aria-checked', on ? 'true' : 'false');
        });
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
            const rl = board.querySelector('#nono-reveal');
            if (rl) while (rl.firstChild) rl.removeChild(rl.firstChild);
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
            actions: (f, m) => {
                const parts = [];
                if (f) parts.push(`fill ${f}`);
                if (m) parts.push(`mark ${m} with ✗`);
                return parts.join(' and ');
            },
            row: (n, clue, act) => `Row ${n}: clue ${clue} → ${act} (highlighted).`,
            col: (n, clue, act) => `Column ${n}: clue ${clue} → ${act} (highlighted).`,
            none: 'Nothing more can be deduced by single-line logic right now.',
        },
        zh: {
            wrong: '醒目標示的格子與唯一解不符——有該留空的格被填了,或該填的格被劃掉了。',
            actions: (f, m) => {
                const parts = [];
                if (f) parts.push(`填滿 ${f} 格`);
                if (m) parts.push(`打叉 ${m} 格`);
                return parts.join('、');
            },
            row: (n, clue, act) => `第 ${n} 列:依線索 ${clue},可${act}(見醒目格)。`,
            col: (n, clue, act) => `第 ${n} 行:依線索 ${clue},可${act}(見醒目格)。`,
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
        // Keep each forced cell's target state (FILL / BLOCK) so the hint can
        // tell the player whether to fill or ✗ it.
        if (step) return { kind: 'deduce', orient: step.orient, index: step.index, clue: step.clue, cells: step.cells };
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
        else {
            const nFill = h.cells.filter((x) => x.state === FILL).length;
            const nMark = h.cells.length - nFill;
            const act = t.actions(nFill, nMark);
            text = (h.orient === 'row' ? t.row : t.col)(h.index + 1, '[' + h.clue.join(' ') + ']', act);
        }
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
            // Spotlight the whole target line.
            if (h.orient === 'row') {
                layer.appendChild(PC.svgEl('rect', { class: 'nono-hint-line', x: ox, y: oy + h.index * cs, width: N * cs, height: cs }));
            } else {
                layer.appendChild(PC.svgEl('rect', { class: 'nono-hint-line', x: ox + h.index * cs, y: oy, width: cs, height: N * cs }));
            }
            // Per cell: a ghost of the suggested action (fill square / ✗) plus a
            // ring. When the solution is revealed we skip the fill ghost (the
            // reveal already shows the fills) but still draw ✗ (reveal has none).
            for (const cell of h.cells) {
                const x0 = ox + cell.c * cs, y0 = oy + cell.r * cs;
                if (cell.state === FILL) {
                    if (!shell.revealed) {
                        layer.appendChild(PC.svgEl('rect', {
                            class: 'nono-hint-fill',
                            x: x0 + cs * 0.21, y: y0 + cs * 0.21, width: cs * 0.58, height: cs * 0.58,
                            rx: cs * 0.1, ry: cs * 0.1,
                        }));
                    }
                } else {
                    const m = cs * 0.3;
                    layer.appendChild(PC.svgEl('line', { class: 'nono-hint-x', x1: x0 + m, y1: y0 + m, x2: x0 + cs - m, y2: y0 + cs - m }));
                    layer.appendChild(PC.svgEl('line', { class: 'nono-hint-x', x1: x0 + cs - m, y1: y0 + m, x2: x0 + m, y2: y0 + cs - m }));
                }
                layer.appendChild(PC.svgEl('rect', {
                    class: 'nono-hint-ring', x: x0 + cs * 0.1, y: y0 + cs * 0.1,
                    width: cs * 0.8, height: cs * 0.8, rx: cs * 0.12, ry: cs * 0.12,
                }));
            }
            return;
        }

        // wrong: red rings around every mismatched cell.
        for (const [r, c] of h.cells) {
            layer.appendChild(PC.svgEl('rect', {
                class: 'nono-hint-ring wrong', x: ox + c * cs + cs * 0.1, y: oy + r * cs + cs * 0.1,
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
        // Reveal overlay lives in its own layer, so it stays on screen even
        // when a hint is shown on top of it (the two no longer fight).
        const layer = board && board.querySelector('#nono-reveal');
        if (!layer) return;
        while (layer.firstChild) layer.removeChild(layer.firstChild);
        if (shell.revealed && !state.won) {
            const p = state.puzzle, N = p.size, { cs, ox, oy } = state;
            for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
                if (p.solution[r][c] === 1) {
                    layer.appendChild(PC.svgEl('rect', {
                        class: 'nono-reveal', x: ox + c * cs + cs * 0.21, y: oy + r * cs + cs * 0.21,
                        width: cs * 0.58, height: cs * 0.58, rx: cs * 0.1, ry: cs * 0.1,
                    }));
                }
            }
        }
        // Re-render any active hint so its fill ghosts appear/disappear to
        // match: while the solution is shown there's no need to re-draw fills.
        repaintHint();
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

        // Cell-state brush selector (Fill / Mark / Clear).
        const tools = document.getElementById('nono-tools');
        if (tools) {
            tools.addEventListener('click', (ev) => {
                const btn = ev.target.closest('.nono-tool');
                if (btn && btn.dataset.mode) setMode(btn.dataset.mode);
            });
        }
        setMode('cycle');

        // Drag-paint game: opt out of the browser's own touch gestures so
        // finger-drags keep firing pointermove instead of scrolling the page.
        // (iOS double-tap-to-zoom is separately handled by the shared shell.)
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
            if ((ev.ctrlKey || ev.metaKey) && !ev.shiftKey && !ev.altKey && (ev.key === 'z' || ev.key === 'Z')) {
                doUndo(); ev.preventDefault();
                return;
            }
            if (ev.ctrlKey || ev.metaKey || ev.altKey) return;
            const k = ev.key.toLowerCase();
            const mode = (k === '1') ? 'cycle'
                : (k === '2' || k === 'f') ? 'fill'
                    : (k === '3' || k === 'x') ? 'block'
                        : (k === '4' || k === 'e') ? 'empty' : null;
            if (mode) { setMode(mode); ev.preventDefault(); }
        });

        shell.start();
    }

    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
})();
