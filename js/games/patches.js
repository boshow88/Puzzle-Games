/**
 * Patches — gameplay + SVG rendering.
 *
 * Consumes puzzles from `window.PuzzleGenerators.patches(size, difficulty,
 * seed, onProgress)` and depends only on window.PuzzleCommon.
 *
 * P1 scope: render the clue board and a Reveal overlay of the solved
 * partition, so the generator can be eyeballed end-to-end. The drag-to-
 * draw interaction, conflict flagging, hints, undo and share land in later
 * passes; the render layers below are already arranged to receive them.
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    const BOARD_SIZE = 480;
    const MIN_SIZE = 5;
    const MAX_SIZE = 12;

    const SQUARE = 'square';
    const WIDE = 'wide';
    const TALL = 'tall';
    const ANY = 'any';

    // Soft, distinguishable palette so adjacent rectangles read apart.
    // Warm-leaning to sit under the red theme without clashing.
    const PATCH_COLORS = [
        '#e5737d', '#e8a15c', '#e6c65b', '#8fc07a',
        '#5cb8a8', '#6aa9e0', '#8f8fe0', '#c684cf',
        '#d98ca6', '#c9925f', '#a6bf6a', '#5fbf9e',
        '#6f9fd8', '#a58fd8', '#d484b0', '#d09090',
    ];

    function clueColor(i) {
        return PATCH_COLORS[((i % PATCH_COLORS.length) + PATCH_COLORS.length)
            % PATCH_COLORS.length];
    }

    // -----------------------------------------------------------------
    // Generation wrapper (adapts the async generator to the shared
    // determinate progress bar — mirrors the other games).
    // -----------------------------------------------------------------

    async function generatePuzzle(size, difficulty, seed) {
        const progress = PC.progress;
        const onProgress = progress
            ? async (fraction) => {
                progress.setFraction(fraction);
                await progress.waitNextPaint();
            }
            : null;
        return window.PuzzleGenerators.patches(size, difficulty, seed, onProgress);
    }

    // -----------------------------------------------------------------
    // State
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,
        placements: [],   // player rectangles (P2); { r, c, w, h, clue }
        won: false,
    };

    let shell = null;
    let board = null;

    function resetPlacements() {
        state.placements = [];
        state.won = false;
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    function cellSize() {
        return BOARD_SIZE / state.puzzle.size;
    }

    function renderBoard() {
        const p = state.puzzle;
        const N = p.size;
        const cs = BOARD_SIZE / N;
        const svg = board;
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        // Layer: cell backgrounds.
        const bg = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                bg.appendChild(PC.svgEl('rect', {
                    class: 'cell-bg',
                    x: c * cs, y: r * cs, width: cs, height: cs,
                    fill: '#ffffff',
                }));
            }
        }
        svg.appendChild(bg);

        // Layer: reveal / placed rectangles (below thin grid + clues).
        const rectsLayer = PC.svgEl('g', { class: 'patch-rects' });
        rectsLayer.setAttribute('id', 'patch-rects');
        svg.appendChild(rectsLayer);

        // Layer: thin interior grid lines.
        const grid = PC.svgEl('g', { class: 'grid' });
        for (let i = 1; i < N; i++) {
            grid.appendChild(PC.svgEl('line', {
                class: 'grid-line',
                x1: i * cs, y1: 0, x2: i * cs, y2: N * cs,
            }));
            grid.appendChild(PC.svgEl('line', {
                class: 'grid-line',
                x1: 0, y1: i * cs, x2: N * cs, y2: i * cs,
            }));
        }
        svg.appendChild(grid);

        // Layer: outer frame.
        const borders = PC.svgEl('g', { class: 'region-borders' });
        const W = N * cs;
        for (const [x1, y1, x2, y2] of [
            [0, 0, W, 0], [0, W, W, W], [0, 0, 0, W], [W, 0, W, W],
        ]) {
            borders.appendChild(PC.svgEl('line', {
                class: 'region-border', x1, y1, x2, y2,
            }));
        }
        svg.appendChild(borders);

        // Layer: clue glyphs.
        const clues = PC.svgEl('g', { class: 'clues' });
        clues.setAttribute('id', 'clues');
        svg.appendChild(clues);

        repaintRects();
        repaintClues();
    }

    /** Draw the solution partition when Reveal is on (P2 will also draw
     *  the player's own placements here). */
    function repaintRects() {
        const p = state.puzzle;
        const cs = cellSize();
        const layer = board.querySelector('#patch-rects');
        while (layer.firstChild) layer.removeChild(layer.firstChild);

        const showSolution = shell.revealed && !state.won;
        const rects = showSolution ? p.solution : state.placements;
        const inset = Math.max(2, cs * 0.06);
        const radius = Math.max(3, cs * 0.10);

        for (const rc of rects) {
            const color = clueColor(rc.clue);
            layer.appendChild(PC.svgEl('rect', {
                class: 'patch-rect' + (showSolution ? ' reveal' : ''),
                x: rc.c * cs + inset,
                y: rc.r * cs + inset,
                width: rc.w * cs - inset * 2,
                height: rc.h * cs - inset * 2,
                rx: radius, ry: radius,
                fill: color,
                stroke: color,
            }));
        }
    }

    function repaintClues() {
        const p = state.puzzle;
        const cs = cellSize();
        const layer = board.querySelector('#clues');
        while (layer.firstChild) layer.removeChild(layer.firstChild);

        p.clues.forEach((clue, i) => {
            const cx = clue.c * cs + cs / 2;
            const cy = clue.r * cs + cs / 2;
            drawClueGlyph(layer, cx, cy, cs, clue, clueColor(i));
        });
    }

    /** A clue marker: a shape swatch tinted with the clue's colour, with
     *  the size number in white when present. 'any' is drawn as a dashed
     *  wide+tall pair, per the spec. */
    function drawClueGlyph(layer, cx, cy, cs, clue, color) {
        const g = PC.svgEl('g', { class: 'clue-glyph' });
        const unit = cs * 0.6;          // long side of the swatch
        const shortSide = unit * 0.62;  // short side for wide/tall
        const rx = Math.max(2, cs * 0.06);

        function swatch(w, h, extra) {
            return PC.svgEl('rect', Object.assign({
                class: 'clue-swatch',
                x: cx - w / 2, y: cy - h / 2, width: w, height: h,
                rx, ry: rx, fill: color,
            }, extra || {}));
        }

        if (clue.shape === SQUARE) {
            g.appendChild(swatch(unit, unit));
        } else if (clue.shape === WIDE) {
            g.appendChild(swatch(unit, shortSide));
        } else if (clue.shape === TALL) {
            g.appendChild(swatch(shortSide, unit));
        } else {
            // any → overlapping dashed wide + tall, translucent.
            const dash = `${Math.max(2, cs * 0.05)} ${Math.max(2, cs * 0.04)}`;
            g.appendChild(swatch(unit, shortSide, {
                class: 'clue-swatch any', fill: color,
                'fill-opacity': 0.28, stroke: color, 'stroke-dasharray': dash,
            }));
            g.appendChild(swatch(shortSide, unit, {
                class: 'clue-swatch any', fill: color,
                'fill-opacity': 0.28, stroke: color, 'stroke-dasharray': dash,
            }));
        }

        if (clue.size != null) {
            const text = PC.svgEl('text', {
                class: 'clue-num',
                x: cx, y: cy,
                'text-anchor': 'middle',
                'dominant-baseline': 'middle',
                dy: '0.02em',
                'font-size': Math.max(11, cs * 0.32),
            });
            text.textContent = String(clue.size);
            g.appendChild(text);
        }
        layer.appendChild(g);
    }

    function updateStatusRow() {
        shell.setWin(state.won);
    }

    // -----------------------------------------------------------------
    // Shell callbacks
    // -----------------------------------------------------------------

    async function startNewGame() {
        const seed = (Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        resetPlacements();
        renderBoard();
        updateStatusRow();
    }

    function resetAction() {
        if (!state.puzzle) return;
        resetPlacements();
        repaintRects();
        repaintClues();
        updateStatusRow();
    }

    function onReveal() {
        repaintRects();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'patches',
            difficulty: { default: 'medium' },
            size: { kind: 'slider', min: MIN_SIZE, max: MAX_SIZE, default: 8 },
            onNewGame: startNewGame,
            onReset: resetAction,
            onReveal,
        });
        board = shell.dom.board;
        board.classList.add('drag-board');
        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
