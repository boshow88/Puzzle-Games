/**
 * Tango — gameplay, dummy puzzle generation, and SVG rendering.
 *
 * Same architectural shape as queens.js (deliberately, so we can refactor
 * the shared parts after both games are settled). Only depends on
 * window.PuzzleCommon.
 *
 * Puzzle JSON contract (so the dummy generator can later be swapped for
 * a real one without touching the UI):
 *   {
 *     id:         string,
 *     game:       'tango',
 *     size:       N,                 // 6, 8 or 10
 *     difficulty: 'easy' | 'medium' | 'hard',
 *     prefilled:  int[N][N],         // 0 empty, 1 sun, 2 moon (locked)
 *     walls: [
 *       { r1, c1, r2, c2, kind }     // kind: 'same' (=) | 'diff' (×)
 *     ],                             // (r1,c1) lex-< (r2,c2), 4-adjacent
 *     solution:   int[N][N],         // 1 sun, 2 moon (always full)
 *   }
 *
 * The current generator is intentionally simple: it produces a random
 * legal solution, then sprinkles prefilled cells and wall constraints
 * matching that solution. It does NOT guarantee a unique solution and
 * has no real difficulty calibration; difficulty only affects how many
 * clues are kept.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const BOARD_SIZE = 480;
    const STATES = { EMPTY: 0, SUN: 1, MOON: 2 };
    const STATE_CYCLE = [STATES.EMPTY, STATES.SUN, STATES.MOON];

    const SYMBOL = {
        [STATES.SUN]: '☀',
        [STATES.MOON]: '☾',
    };

    const VIOLATION_DELAY_MS = 800;

    const VALID_SIZES = [6, 8, 10];

    // Fraction of cells / wall-slots seeded by the dummy generator,
    // indexed by difficulty. Tuned by eyeballing playability — the proper
    // difficulty model will arrive with the real generator.
    const CLUE_DENSITY = {
        easy:   { prefill: 0.45, wall: 0.30 },
        medium: { prefill: 0.30, wall: 0.20 },
        hard:   { prefill: 0.18, wall: 0.12 },
    };

    // -----------------------------------------------------------------
    // Dummy puzzle generator
    // -----------------------------------------------------------------

    /**
     * Build a random valid Tango solution grid by randomised backtracking.
     * Returns int[N][N] of 1/2, or null if it failed within the search.
     */
    function placeValidGrid(N, rng) {
        const half = N / 2;
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        const rowSun = new Array(N).fill(0);
        const rowMoon = new Array(N).fill(0);
        const colSun = new Array(N).fill(0);
        const colMoon = new Array(N).fill(0);

        function fits(r, c, v) {
            if (v === STATES.SUN) {
                if (rowSun[r] >= half) return false;
                if (colSun[c] >= half) return false;
            } else {
                if (rowMoon[r] >= half) return false;
                if (colMoon[c] >= half) return false;
            }
            // No three in a row horizontally
            if (c >= 2 && grid[r][c - 1] === v && grid[r][c - 2] === v) return false;
            // No three in a row vertically
            if (r >= 2 && grid[r - 1][c] === v && grid[r - 2][c] === v) return false;
            return true;
        }

        function set(r, c, v) {
            grid[r][c] = v;
            if (v === STATES.SUN) { rowSun[r]++; colSun[c]++; }
            else { rowMoon[r]++; colMoon[c]++; }
        }
        function unset(r, c, v) {
            grid[r][c] = 0;
            if (v === STATES.SUN) { rowSun[r]--; colSun[c]--; }
            else { rowMoon[r]--; colMoon[c]--; }
        }

        function solve(idx) {
            if (idx === N * N) return true;
            const r = Math.floor(idx / N);
            const c = idx % N;
            const choices = [STATES.SUN, STATES.MOON];
            PC.rng.shuffle(choices, rng);
            for (const v of choices) {
                if (!fits(r, c, v)) continue;
                set(r, c, v);
                if (solve(idx + 1)) return true;
                unset(r, c, v);
            }
            return false;
        }

        return solve(0) ? grid : null;
    }

    /**
     * Sprinkle prefilled clues by copying ~fraction of cells from the
     * solution. Returns int[N][N] (0 / 1 / 2).
     */
    function chooseClues(N, solution, fraction, rng) {
        const out = Array.from({ length: N }, () => new Array(N).fill(0));
        const all = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) all.push([r, c]);
        }
        PC.rng.shuffle(all, rng);
        const take = Math.round(all.length * fraction);
        for (let i = 0; i < take; i++) {
            const [r, c] = all[i];
            out[r][c] = solution[r][c];
        }
        return out;
    }

    /**
     * Pick a subset of adjacent-cell pairs to carry `=` / `×` wall
     * constraints. The kind always matches the solution, so the puzzle
     * remains solvable from the clues.
     */
    function chooseWalls(N, solution, fraction, rng) {
        const slots = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (c + 1 < N) slots.push([r, c, r, c + 1]);
                if (r + 1 < N) slots.push([r, c, r + 1, c]);
            }
        }
        PC.rng.shuffle(slots, rng);
        const take = Math.round(slots.length * fraction);
        const out = [];
        for (let i = 0; i < take; i++) {
            const [r1, c1, r2, c2] = slots[i];
            const kind = solution[r1][c1] === solution[r2][c2] ? 'same' : 'diff';
            out.push({ r1, c1, r2, c2, kind });
        }
        return out;
    }

    function generatePuzzle(size, difficulty, seed) {
        const rng = PC.rng.make(seed);
        let solution = null;
        for (let i = 0; i < 8 && !solution; i++) {
            solution = placeValidGrid(size, rng);
        }
        if (!solution) {
            // Should be vanishingly rare; fall back to a known striped grid.
            solution = Array.from({ length: size }, (_, r) =>
                Array.from({ length: size }, (_, c) =>
                    ((r + c) % 2 === 0 ? STATES.SUN : STATES.MOON)
                )
            );
        }
        const density = CLUE_DENSITY[difficulty] || CLUE_DENSITY.medium;
        const prefilled = chooseClues(size, solution, density.prefill, rng);
        const walls = chooseWalls(size, solution, density.wall, rng);
        return {
            id: `tango-${size}x${size}-${difficulty}-${seed.toString(36)}`,
            game: 'tango',
            size,
            difficulty,
            prefilled,
            walls,
            solution,
        };
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        placements: null,           // int[N][N] of STATES.*; for prefilled cells stays 0
        revealed: false,
        won: false,
        size: 8,
        difficulty: 'medium',

        violations: null,           // bool[N][N] truth (used for win check)
        conflictPairs: 0,
        displayedViolations: null,
        displayedPairs: 0,
        violationTimer: null,

        timer: null,
    };

    function emptyViolationGrid(N) {
        return Array.from({ length: N }, () => new Array(N).fill(false));
    }

    function ensurePlacementsForCurrent() {
        const N = state.puzzle.size;
        state.placements = Array.from({ length: N }, () => new Array(N).fill(STATES.EMPTY));
        state.violations = emptyViolationGrid(N);
        state.conflictPairs = 0;
        state.displayedViolations = emptyViolationGrid(N);
        state.displayedPairs = 0;
        cancelViolationTimer();
        state.won = false;
    }

    function cancelViolationTimer() {
        if (state.violationTimer) {
            clearTimeout(state.violationTimer);
            state.violationTimer = null;
        }
    }

    function commitViolationDisplay() {
        state.violationTimer = null;
        if (!state.violations) return;
        state.displayedViolations = state.violations.map((row) => row.slice());
        state.displayedPairs = state.conflictPairs;
        repaintSymbols();
        updateStatusRow();
    }

    /** Effective symbol at a cell (prefilled if locked, otherwise player). */
    function effective(r, c) {
        const e = state.puzzle.prefilled[r][c];
        return e !== STATES.EMPTY ? e : state.placements[r][c];
    }

    function isPrefilled(r, c) {
        return state.puzzle.prefilled[r][c] !== STATES.EMPTY;
    }

    // -----------------------------------------------------------------
    // Rules
    // -----------------------------------------------------------------

    function recomputeViolations() {
        const N = state.puzzle.size;
        const half = N / 2;
        const flagged = emptyViolationGrid(N);
        let pairs = 0;

        // Counts per row and column.
        const rowSun = new Array(N).fill(0);
        const rowMoon = new Array(N).fill(0);
        const colSun = new Array(N).fill(0);
        const colMoon = new Array(N).fill(0);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = effective(r, c);
                if (v === STATES.SUN) { rowSun[r]++; colSun[c]++; }
                else if (v === STATES.MOON) { rowMoon[r]++; colMoon[c]++; }
            }
        }

        // Row / column count overflow: more than half of either symbol.
        // Flag every offending cell of the over-represented symbol.
        for (let r = 0; r < N; r++) {
            if (rowSun[r] > half) {
                for (let c = 0; c < N; c++) {
                    if (effective(r, c) === STATES.SUN) flagged[r][c] = true;
                }
                pairs += 1;
            }
            if (rowMoon[r] > half) {
                for (let c = 0; c < N; c++) {
                    if (effective(r, c) === STATES.MOON) flagged[r][c] = true;
                }
                pairs += 1;
            }
        }
        for (let c = 0; c < N; c++) {
            if (colSun[c] > half) {
                for (let r = 0; r < N; r++) {
                    if (effective(r, c) === STATES.SUN) flagged[r][c] = true;
                }
                pairs += 1;
            }
            if (colMoon[c] > half) {
                for (let r = 0; r < N; r++) {
                    if (effective(r, c) === STATES.MOON) flagged[r][c] = true;
                }
                pairs += 1;
            }
        }

        // Three-in-a-row in rows (each maximal run of length >= 3 counts once).
        for (let r = 0; r < N; r++) {
            let runStart = 0;
            let runVal = effective(r, 0);
            for (let c = 1; c <= N; c++) {
                const v = c < N ? effective(r, c) : -1;
                if (v !== runVal) {
                    const runLen = c - runStart;
                    if (runVal !== STATES.EMPTY && runLen >= 3) {
                        for (let k = runStart; k < c; k++) flagged[r][k] = true;
                        pairs += 1;
                    }
                    runStart = c;
                    runVal = v;
                }
            }
        }
        for (let c = 0; c < N; c++) {
            let runStart = 0;
            let runVal = effective(0, c);
            for (let r = 1; r <= N; r++) {
                const v = r < N ? effective(r, c) : -1;
                if (v !== runVal) {
                    const runLen = r - runStart;
                    if (runVal !== STATES.EMPTY && runLen >= 3) {
                        for (let k = runStart; k < r; k++) flagged[k][c] = true;
                        pairs += 1;
                    }
                    runStart = r;
                    runVal = v;
                }
            }
        }

        // Wall constraints.
        for (const w of state.puzzle.walls) {
            const a = effective(w.r1, w.c1);
            const b = effective(w.r2, w.c2);
            if (a === STATES.EMPTY || b === STATES.EMPTY) continue;
            const broken = (w.kind === 'same' && a !== b)
                        || (w.kind === 'diff' && a === b);
            if (broken) {
                flagged[w.r1][w.c1] = true;
                flagged[w.r2][w.c2] = true;
                pairs += 1;
            }
        }

        state.violations = flagged;
        state.conflictPairs = pairs;
    }

    function isFullyFilled() {
        const N = state.puzzle.size;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (effective(r, c) === STATES.EMPTY) return false;
            }
        }
        return true;
    }

    function checkWin() {
        recomputeViolations();
        return isFullyFilled() && state.conflictPairs === 0;
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    const dom = {
        board: null,
        difficultySeg: null,
        sizeSeg: null,
        newGameBtn: null,
        resetBtn: null,
        revealBtn: null,
        timer: null,
        violations: null,
        violationsText: null,
        winMessage: null,
    };

    function cellRect(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { x: c * cs, y: r * cs, size: cs };
    }

    function renderBoard() {
        const N = state.puzzle.size;
        const svg = dom.board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        const cs = BOARD_SIZE / N;

        // Layer: cell backgrounds (light fill; prefilled get a darker tint).
        const bgGroup = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const cls = 'cell-bg' + (isPrefilled(r, c) ? ' prefilled' : '');
                bgGroup.appendChild(PC.svgEl('rect', {
                    class: cls,
                    x, y, width: size, height: size,
                    fill: isPrefilled(r, c) ? '#e6e8ee' : '#ffffff',
                }));
            }
        }
        svg.appendChild(bgGroup);

        // Layer: outer frame (same stroke style as Queens' region borders).
        const borderGroup = PC.svgEl('g', { class: 'region-borders' });
        const W = N * cs;
        const addBorder = (x1, y1, x2, y2) => {
            borderGroup.appendChild(PC.svgEl('line', {
                class: 'region-border', x1, y1, x2, y2,
            }));
        };
        addBorder(0, 0, W, 0);
        addBorder(0, W, W, W);
        addBorder(0, 0, 0, W);
        addBorder(W, 0, W, W);
        svg.appendChild(borderGroup);

        // Layer: symbols + violations + reveal hint (rebuilt every repaint).
        const symbolGroup = PC.svgEl('g', { class: 'symbols' });
        symbolGroup.setAttribute('id', 'symbols');
        svg.appendChild(symbolGroup);

        // Layer: wall badges (=/× glyphs sitting directly on the cell
        // boundary; no background — just the symbol on top of the grid).
        const wallGroup = PC.svgEl('g', { class: 'walls' });
        const glyphSize = Math.max(13, Math.floor(cs * 0.42));
        for (const w of state.puzzle.walls) {
            const x = ((w.c1 + w.c2 + 1) * cs) / 2;
            const y = ((w.r1 + w.r2 + 1) * cs) / 2;
            const t = PC.svgEl('text', {
                class: 'wall-glyph',
                x, y,
                'text-anchor': 'middle',
                'dominant-baseline': 'middle',
                dy: '0.04em',
                'font-size': glyphSize,
            });
            t.textContent = w.kind === 'same' ? '=' : '×';
            wallGroup.appendChild(t);
        }
        svg.appendChild(wallGroup);

        // Layer: invisible click targets (last, so they sit on top).
        const hitGroup = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                if (isPrefilled(r, c)) continue; // prefilled cells aren't clickable
                hitGroup.appendChild(PC.svgEl('rect', {
                    class: 'cell-hover',
                    x, y, width: size, height: size,
                    'data-r': r,
                    'data-c': c,
                }));
            }
        }
        svg.appendChild(hitGroup);

        repaintSymbols();
    }

    function repaintSymbols() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const group = dom.board.querySelector('#symbols');
        while (group.firstChild) group.removeChild(group.firstChild);

        const symbolFont = Math.max(16, Math.floor(cs * 0.55));

        // Symbols (prefilled + player)
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const v = effective(r, c);
                if (v === STATES.EMPTY) continue;
                const cx = c * cs + cs / 2;
                const cy = r * cs + cs / 2;
                const symbolKind = v === STATES.SUN ? 'sun' : 'moon';
                const lockedClass = isPrefilled(r, c) ? ' prefilled' : '';
                const text = PC.svgEl('text', {
                    class: `symbol ${symbolKind}${lockedClass}`,
                    x: cx, y: cy,
                    'text-anchor': 'middle',
                    'dominant-baseline': 'middle',
                    dy: '0.08em',
                    'font-size': symbolFont,
                });
                text.textContent = SYMBOL[v];
                group.appendChild(text);
            }
        }

        // Violations (read from the debounced display buffer)
        const vis = state.displayedViolations;
        if (vis) {
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (!vis[r][c]) continue;
                    const inset = Math.max(4, cs * 0.18);
                    const x1 = c * cs + inset;
                    const y1 = r * cs + inset;
                    const x2 = (c + 1) * cs - inset;
                    const y2 = (r + 1) * cs - inset;
                    group.appendChild(PC.svgEl('line', {
                        class: 'violation-line',
                        x1, y1, x2, y2,
                    }));
                    group.appendChild(PC.svgEl('line', {
                        class: 'violation-line',
                        x1: x2, y1: y1, x2: x1, y2: y2,
                    }));
                }
            }
        }

        // Reveal: tiny solution symbol in the top-left corner of each
        // *player-editable* cell. Prefilled cells already display the
        // correct answer, so they don't need the hint.
        if (state.revealed && state.puzzle && state.puzzle.solution) {
            const sol = state.puzzle.solution;
            const hintFont = Math.max(9, Math.floor(cs * 0.22));
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (isPrefilled(r, c)) continue;
                    const text = PC.svgEl('text', {
                        class: 'symbol reveal-hint',
                        x: c * cs + cs * 0.16,
                        y: r * cs + cs * 0.18,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.08em',
                        'font-size': hintFont,
                    });
                    text.textContent = SYMBOL[sol[r][c]];
                    group.appendChild(text);
                }
            }
        }
    }

    function updateStatusRow() {
        const v = state.displayedPairs;
        if (v > 0) {
            dom.violations.hidden = false;
            dom.violations.classList.add('active');
            dom.violationsText.textContent =
                `⚠ ${v} conflict${v === 1 ? '' : 's'}`;
        } else {
            dom.violations.hidden = true;
            dom.violations.classList.remove('active');
        }
        dom.winMessage.hidden = !state.won;
    }

    // -----------------------------------------------------------------
    // Event handlers
    // -----------------------------------------------------------------

    function cycleCell(r, c) {
        if (!state.puzzle || state.won) return;
        if (isPrefilled(r, c)) return;
        const cur = state.placements[r][c];
        const idx = STATE_CYCLE.indexOf(cur);
        state.placements[r][c] = STATE_CYCLE[(idx + 1) % STATE_CYCLE.length];

        const won = checkWin();
        if (won && !state.won) {
            state.won = true;
            cancelViolationTimer();
            state.displayedViolations = emptyViolationGrid(state.puzzle.size);
            state.displayedPairs = 0;
            const elapsed = state.timer ? state.timer.stop() : 0;
            PC.solves.log('tango', state.puzzle.size, state.puzzle.difficulty, elapsed);
            repaintSymbols();
            updateStatusRow();
            return;
        }

        cancelViolationTimer();
        state.displayedViolations = emptyViolationGrid(state.puzzle.size);
        state.displayedPairs = 0;
        repaintSymbols();
        updateStatusRow();
        state.violationTimer = setTimeout(commitViolationDisplay, VIOLATION_DELAY_MS);
    }

    function onBoardClick(ev) {
        const target = ev.target.closest('rect.cell-hover');
        if (!target) return;
        const r = parseInt(target.getAttribute('data-r'), 10);
        const c = parseInt(target.getAttribute('data-c'), 10);
        cycleCell(r, c);
    }

    function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = generatePuzzle(state.size, state.difficulty, seed);
        ensurePlacementsForCurrent();
        state.revealed = false;
        dom.revealBtn.classList.remove('active');
        dom.revealBtn.setAttribute('aria-pressed', 'false');
        renderBoard();
        updateStatusRow();
        if (state.timer) state.timer.start();
    }

    function resetPlacements() {
        if (!state.puzzle) return;
        ensurePlacementsForCurrent();
        state.won = false;
        repaintSymbols();
        updateStatusRow();
        if (state.timer) state.timer.start();
    }

    function toggleReveal() {
        state.revealed = !state.revealed;
        dom.revealBtn.classList.toggle('active', state.revealed);
        dom.revealBtn.setAttribute('aria-pressed', state.revealed ? 'true' : 'false');
        repaintSymbols();
    }

    function setDifficulty(value) {
        if (!['easy', 'medium', 'hard'].includes(value)) return;
        state.difficulty = value;
        dom.difficultySeg.querySelectorAll('button').forEach((btn) => {
            btn.classList.toggle('active', btn.dataset.value === value);
        });
        PC.prefs.set('tango', { difficulty: value });
        startNewGame();
    }

    function setSize(value) {
        const n = parseInt(value, 10);
        if (!VALID_SIZES.includes(n)) return;
        state.size = n;
        dom.sizeSeg.querySelectorAll('button').forEach((btn) => {
            btn.classList.toggle('active', parseInt(btn.dataset.value, 10) === n);
        });
        PC.prefs.set('tango', { size: n });
        startNewGame();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        dom.board = document.getElementById('board');
        dom.difficultySeg = document.getElementById('difficulty-seg');
        dom.sizeSeg = document.getElementById('size-seg');
        dom.newGameBtn = document.getElementById('new-game-btn');
        dom.resetBtn = document.getElementById('reset-btn');
        dom.revealBtn = document.getElementById('reveal-btn');
        dom.timer = document.getElementById('timer');
        dom.violations = document.getElementById('violations');
        dom.violationsText = document.getElementById('violations-text');
        dom.winMessage = document.getElementById('win-message');

        const prefs = PC.prefs.get('tango');
        if (prefs.difficulty) state.difficulty = prefs.difficulty;
        if (prefs.size && VALID_SIZES.includes(prefs.size)) state.size = prefs.size;

        dom.difficultySeg.querySelectorAll('button').forEach((btn) => {
            btn.classList.toggle('active', btn.dataset.value === state.difficulty);
            btn.addEventListener('click', () => setDifficulty(btn.dataset.value));
        });
        dom.sizeSeg.querySelectorAll('button').forEach((btn) => {
            btn.classList.toggle('active', parseInt(btn.dataset.value, 10) === state.size);
            btn.addEventListener('click', () => setSize(btn.dataset.value));
        });

        dom.newGameBtn.addEventListener('click', startNewGame);
        dom.resetBtn.addEventListener('click', resetPlacements);
        dom.revealBtn.addEventListener('click', toggleReveal);
        dom.board.addEventListener('click', onBoardClick);

        state.timer = PC.timer(dom.timer);
        startNewGame();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
