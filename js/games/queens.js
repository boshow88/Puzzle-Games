/**
 * Queens — gameplay + SVG rendering.
 *
 * Puzzle generation lives in `js/generators/queens.js` and is exposed
 * via `window.PuzzleGenerators.queens(size, difficulty, seed, onProgress)`.
 *
 * Puzzle JSON shape:
 *   {
 *     id:         string,
 *     game:       'queens',
 *     size:       N,
 *     difficulty: 'easy' | 'medium' | 'hard',
 *     regions:    int[N][N],          // regions[r][c] ∈ [0, N-1]
 *     solution:   int[N],             // solution[r] = column of queen
 *     stats?:     { ... },            // generator bookkeeping
 *   }
 */
(function () {
    'use strict';

    const PC = window.PuzzleCommon;

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------

    const REGION_COLORS = [
        '#FF8888', '#FFB366', '#FFDD33', '#66DD66',
        '#7799FF', '#BB77DD', '#FF88CC', '#DD8855',
        '#88DDDD', '#DDAA77', '#99BB99', '#CCAAFF',
    ];

    // Multiplicative darken of a `#RRGGBB` hex — used to derive the
    // in-family stripe colour that a hint's "excluded" cells wear
    // (region colour × factor). Kept tolerant of `#rgb` shorthand
    // even though REGION_COLORS is always full-length.
    function darkenHex(hex, factor) {
        const h = hex.replace('#', '');
        const full = h.length === 3
            ? h.split('').map((c) => c + c).join('')
            : h;
        const r = parseInt(full.slice(0, 2), 16);
        const g = parseInt(full.slice(2, 4), 16);
        const b = parseInt(full.slice(4, 6), 16);
        const clamp = (v) => Math.max(0, Math.min(255, Math.round(v)));
        const toHex = (v) => clamp(v).toString(16).padStart(2, '0');
        return '#' + toHex(r * factor) + toHex(g * factor) + toHex(b * factor);
    }

    const BOARD_SIZE = 480; // logical board area; SVG viewBox adds padding for outer stroke
    const STATES = { EMPTY: 0, MARK: 1, QUEEN: 2 };
    const STATE_CYCLE = [STATES.EMPTY, STATES.MARK, STATES.QUEEN]; // click order

    // Delay before red violation slashes appear after a placement change.
    // Matches the tk backup's "don't pester the player while they're still
    // cycling cells" behaviour.
    const VIOLATION_DELAY_MS = 800;

    // -----------------------------------------------------------------
    // Puzzle generation (thin wrapper around the async generator).
    //
    // Mirrors Tango's shape: the generator drives a determinate-friendly
    // progress callback, the game just adapts that into the shared
    // `PC.progress` UI.
    // -----------------------------------------------------------------

    async function generatePuzzle(size, difficulty, seed) {
        const progress = PC.progress;
        const onProgress = progress
            ? async (fraction) => {
                progress.setFraction(fraction);
                await progress.waitNextPaint();
            }
            : null;
        return window.PuzzleGenerators.queens(size, difficulty, seed, onProgress);
    }

    // -----------------------------------------------------------------
    // Game state
    // -----------------------------------------------------------------

    const state = {
        puzzle: null,                   // current puzzle JSON
        placements: null,               // int[N][N] of STATES.*
        won: false,

        // Two layers of violation state:
        //   `violations` / `conflictPairs`           — recomputed instantly,
        //                                              used to decide win.
        //   `displayedViolations` / `displayedPairs` — what the UI shows,
        //                                              committed only after
        //                                              VIOLATION_DELAY_MS of
        //                                              no further clicks.
        violations: null,
        violationGroups: [],        // [{ kind, cells }] for partial refresh
        conflictPairs: 0,
        displayedViolations: null,
        displayedPairs: 0,
        violationTimer: null,

        // Active hint. See renderHintBanner / repaintHintOverlay for the
        // shape. Cleared whenever the player alters a ♛ (× toggles do
        // not affect the solver, so we leave them alone).
        hint: null,
        hintBanner: null,
        hintButton: null,
    };

    // The shell owns difficulty / size / revealed / timer.
    let shell = null;

    // Active pointer gesture. Modes:
    //   'mark'           — started on an empty cell. The starting cell
    //                      was already flipped to × at pointerdown time
    //                      (a tap-on-empty does the same thing). Every
    //                      subsequent empty cell the finger enters also
    //                      becomes ×.
    //   'unmark-pending' — started on ×. Ambiguous: could be a tap that
    //                      wants × → ♛, or a drag that wants to erase ×s.
    //                      We defer until the pointer leaves the start;
    //                      the first move commits us into 'unmark'.
    //   'unmark'         — committed drag-erase. The starting cell has
    //                      been cleared to empty and every × the finger
    //                      passes over gets cleared too.
    //   'tap'            — started on ♛. Pure tap: cycle only if the
    //                      release lands back on the same cell.
    let dragState = null;

    function emptyViolationGrid(N) {
        return Array.from({ length: N }, () => new Array(N).fill(false));
    }

    function ensurePlacementsForCurrent() {
        const N = state.puzzle.size;
        state.placements = Array.from({ length: N }, () => new Array(N).fill(STATES.EMPTY));
        state.violations = emptyViolationGrid(N);
        state.violationGroups = [];
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

    // -----------------------------------------------------------------
    // Rules
    // -----------------------------------------------------------------

    /**
     * Recompute violations from current placements. Two views are
     * produced: a cell-level `flagged` grid (used for the win check and
     * the 800ms-debounced full display), and a list of `groups` where
     * each group is a pair of queens that breaks at least one rule. The
     * group view lets the partial-refresh logic hide only the conflicts
     * that the latest toggle could possibly have affected.
     *
     * Returns the list of queen positions so callers can avoid scanning
     * the board twice.
     */
    function recomputeViolations() {
        const N = state.puzzle.size;
        const regions = state.puzzle.regions;
        const queens = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.placements[r][c] === STATES.QUEEN) {
                    queens.push([r, c]);
                }
            }
        }
        const flagged = emptyViolationGrid(N);
        const groups = [];

        // A "conflict pair" is two queens that violate ANY rule (a pair
        // that breaks multiple rules still counts as one).
        for (let i = 0; i < queens.length; i++) {
            const [r1, c1] = queens[i];
            for (let j = i + 1; j < queens.length; j++) {
                const [r2, c2] = queens[j];
                const sameRow = r1 === r2;
                const sameCol = c1 === c2;
                const adj8 = Math.abs(r1 - r2) <= 1 && Math.abs(c1 - c2) <= 1;
                const sameRegion = regions[r1][c1] === regions[r2][c2];
                if (sameRow || sameCol || adj8 || sameRegion) {
                    flagged[r1][c1] = true;
                    flagged[r2][c2] = true;
                    groups.push({ kind: 'pair', cells: [[r1, c1], [r2, c2]] });
                }
            }
        }
        state.violations = flagged;
        state.violationGroups = groups;
        state.conflictPairs = groups.length;
        return queens;
    }

    /**
     * A pair-conflict between two queens is "owned by" a toggle at
     * (r0, c0) iff (r0, c0) is one of the two queens involved. The
     * conflict between two OTHER queens cannot change as a result of
     * the toggle, so it stays on screen.
     */
    function isGroupOwnedBy(group, r0, c0) {
        return group.cells.some(([r, c]) => r === r0 && c === c0);
    }

    function checkWin() {
        const N = state.puzzle.size;
        // Count queens from the flagged grid's source (state.placements)
        // — caller must have run `recomputeViolations` already.
        let queenCount = 0;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.placements[r][c] === STATES.QUEEN) queenCount += 1;
            }
        }
        return queenCount === N && state.conflictPairs === 0;
    }

    /**
     * Refresh the displayed-violation overlay after a toggle at (r0, c0).
     * Conflicts whose group is NOT owned by the toggle stay visible
     * immediately. Conflicts that ARE owned are hidden for
     * VIOLATION_DELAY_MS, after which commitViolationDisplay flushes
     * the full set.
     */
    function scheduleViolationRefresh(r0, c0) {
        cancelViolationTimer();
        const N = state.puzzle.size;
        const visible = emptyViolationGrid(N);
        let count = 0;
        for (const g of state.violationGroups || []) {
            if (isGroupOwnedBy(g, r0, c0)) continue;
            count += 1;
            for (const [r, c] of g.cells) visible[r][c] = true;
        }
        state.displayedViolations = visible;
        state.displayedPairs = count;
        state.violationTimer = setTimeout(commitViolationDisplay, VIOLATION_DELAY_MS);
    }

    // -----------------------------------------------------------------
    // Rendering
    // -----------------------------------------------------------------

    // Only the board needs a long-lived ref here — the shell owns the
    // toolbar / status row DOM.
    let board = null;

    function regionColor(idx) {
        return REGION_COLORS[idx % REGION_COLORS.length];
    }

    function cellRect(N, r, c) {
        const cs = BOARD_SIZE / N;
        return { x: c * cs, y: r * cs, size: cs };
    }

    function renderBoard() {
        const N = state.puzzle.size;
        const regions = state.puzzle.regions;
        const svg = board;
        // Clear
        while (svg.firstChild) svg.removeChild(svg.firstChild);

        const cs = BOARD_SIZE / N;

        // Layer: <defs> — one stripe pattern per region colour, used by
        // hint "excluded" cells. Using in-family shades (darkenHex of
        // the region colour) keeps the striping tonally consistent
        // with the cell it sits on instead of jarring bright red.
        // Patterns are namespaced `queens-hint-stripes-<idx>`.
        const defs = PC.svgEl('defs', {});
        for (let k = 0; k < REGION_COLORS.length; k++) {
            // Thin, low-opacity, in-palette stripes. Just enough of a
            // texture cue to read as "excluded" without competing with
            // the region colour or the × / ♛ glyphs the player is
            // trying to focus on.
            const stripe = darkenHex(REGION_COLORS[k], 0.7);
            const pat = PC.svgEl('pattern', {
                id: `queens-hint-stripes-${k}`,
                patternUnits: 'userSpaceOnUse',
                width: 8, height: 8,
                patternTransform: 'rotate(45)',
            });
            pat.appendChild(PC.svgEl('line', {
                x1: 0, y1: 0, x2: 0, y2: 8,
                stroke: stripe, 'stroke-width': 2, 'stroke-opacity': 0.4,
            }));
            defs.appendChild(pat);
        }
        svg.appendChild(defs);

        // Layer: cell backgrounds (colored by region)
        const bgGroup = PC.svgEl('g', { class: 'cells' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const rect = PC.svgEl('rect', {
                    class: 'cell-bg',
                    x, y, width: size, height: size,
                    fill: regionColor(regions[r][c]),
                });
                bgGroup.appendChild(rect);
            }
        }
        svg.appendChild(bgGroup);

        // Layer: hint FILL — sits above cell backgrounds so its
        // semi-transparent tints show through the region colours, but
        // below the region borders so those stay crisp even inside the
        // highlighted area. Populated / cleared by repaintHintOverlay.
        const hintFillGroup = PC.svgEl('g', { class: 'hint-fill' });
        hintFillGroup.setAttribute('id', 'hint-fill');
        svg.appendChild(hintFillGroup);

        // Layer: region borders (thick lines between differing regions and
        // around the outer perimeter — same stroke width everywhere). The
        // SVG viewBox has 3px of padding so the outer stroke isn't clipped.
        const borderGroup = PC.svgEl('g', { class: 'region-borders' });
        const addBorder = (x1, y1, x2, y2) => {
            borderGroup.appendChild(PC.svgEl('line', {
                class: 'region-border', x1, y1, x2, y2,
            }));
        };
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const rid = regions[r][c];
                const { x, y, size } = cellRect(N, r, c);
                if (r === 0 || regions[r - 1][c] !== rid) {
                    addBorder(x, y, x + size, y);
                }
                if (c === 0 || regions[r][c - 1] !== rid) {
                    addBorder(x, y, x, y + size);
                }
                if (r === N - 1) addBorder(x, y + size, x + size, y + size);
                if (c === N - 1) addBorder(x + size, y, x + size, y + size);
            }
        }
        svg.appendChild(borderGroup);

        // Layer: hint OUTLINE — bold coloured strokes drawn above the
        // region borders so they cut through and clearly frame the
        // hint cells regardless of what region colour they sit on.
        const hintOutlineGroup = PC.svgEl('g', { class: 'hint-outline' });
        hintOutlineGroup.setAttribute('id', 'hint-outline');
        svg.appendChild(hintOutlineGroup);

        // Layer: symbols (queen / mark) + violations + reveal overlay
        const symbolGroup = PC.svgEl('g', { class: 'symbols' });
        symbolGroup.setAttribute('id', 'symbols');
        svg.appendChild(symbolGroup);

        // Layer: hint DIM — a per-cell black tint painted over every
        // NON-hint cell (including its symbols) when a hint is active.
        // This produces the "spotlight" effect the design calls for:
        // the important cells stay at full brightness, everything else
        // fades back. Below the hit layer so pointer events still work.
        const hintDimGroup = PC.svgEl('g', { class: 'hint-dim' });
        hintDimGroup.setAttribute('id', 'hint-dim');
        svg.appendChild(hintDimGroup);

        // Layer: invisible click targets (placed last so they capture events)
        const hitGroup = PC.svgEl('g', { class: 'hit' });
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const { x, y, size } = cellRect(N, r, c);
                const hit = PC.svgEl('rect', {
                    class: 'cell-hover',
                    x, y, width: size, height: size,
                    'data-r': r,
                    'data-c': c,
                });
                hitGroup.appendChild(hit);
            }
        }
        svg.appendChild(hitGroup);

        repaintSymbols();
        repaintHintOverlay();
    }

    function repaintSymbols() {
        const N = state.puzzle.size;
        const cs = BOARD_SIZE / N;
        const group = board.querySelector('#symbols');
        while (group.firstChild) group.removeChild(group.firstChild);

        const symbolFont = Math.max(14, Math.floor(cs * 0.55));
        const markFont = Math.max(12, Math.floor(cs * 0.45));

        // Player symbols
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const s = state.placements[r][c];
                if (s === STATES.EMPTY) continue;
                const cx = c * cs + cs / 2;
                const cy = r * cs + cs / 2;
                if (s === STATES.QUEEN) {
                    const cls = 'symbol queen' + (state.won ? ' victory' : '');
                    const text = PC.svgEl('text', {
                        class: cls,
                        x: cx, y: cy,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.10em',
                        'font-size': symbolFont,
                    });
                    text.textContent = '♛';
                    group.appendChild(text);
                } else if (s === STATES.MARK) {
                    const text = PC.svgEl('text', {
                        class: 'symbol mark',
                        x: cx, y: cy,
                        'text-anchor': 'middle',
                        'dominant-baseline': 'middle',
                        dy: '0.04em',
                        'font-size': markFont,
                    });
                    text.textContent = '×';
                    group.appendChild(text);
                }
            }
        }

        // Violations (read from the *displayed* buffer, which is debounced)
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

        // Solution overlay (Reveal). Always shown — even when the cell has a
        // player mark or queen — but kept tiny in the corner so it never
        // collides with the player's main symbol (which is centered).
        if (shell.revealed && state.puzzle && state.puzzle.solution) {
            const sol = state.puzzle.solution;
            const hintFont = Math.max(9, Math.floor(cs * 0.24));
            for (let r = 0; r < N; r++) {
                const c = sol[r];
                const text = PC.svgEl('text', {
                    class: 'symbol reveal-hint',
                    x: c * cs + cs * 0.15,
                    y: r * cs + cs * 0.18,
                    'text-anchor': 'middle',
                    'dominant-baseline': 'middle',
                    dy: '0.10em',
                    'font-size': hintFont,
                });
                text.textContent = '♛';
                group.appendChild(text);
            }
        }
    }

    function updateStatusRow() {
        shell.setViolationCount(state.displayedPairs);
        shell.setWin(state.won);
    }

    // -----------------------------------------------------------------
    // Event handlers
    // -----------------------------------------------------------------

    // Transition a single cell to the given state. Only ♛ transitions
    // can create or dissolve a violation / win, so pure × toggles skip
    // the recompute — that keeps a fast drag-mark from paying the O(N²)
    // scan on every intermediate cell.
    //
    // While a hint is active, the board is frozen except for the cells
    // that hint touches — the player is nudged towards completing the
    // hint before doing anything else. When the hint's requirement is
    // met the hint auto-dismisses so the player keeps flow without
    // having to click Hint again.
    function applyCellState(r, c, next) {
        if (!state.puzzle || state.won) return;
        if (state.hint && !isHintCell(r, c)) return;
        const cur = state.placements[r][c];
        if (cur === next) return;
        state.placements[r][c] = next;

        const queenInvolved = cur === STATES.QUEEN || next === STATES.QUEEN;
        if (queenInvolved) {
            recomputeViolations();
            if (checkWin() && !state.won) {
                state.won = true;
                cancelViolationTimer();
                state.displayedViolations = emptyViolationGrid(state.puzzle.size);
                state.displayedPairs = 0;
                shell.markSolved();
                clearHint();
                repaintSymbols();
                updateStatusRow();
                return;
            }
            // Show unrelated conflicts immediately; debounce the ones
            // owned by this toggle for VIOLATION_DELAY_MS so the red
            // slashes don't flash distractingly while the player is
            // still cycling through states in the same row / col /
            // region / neighbourhood.
            scheduleViolationRefresh(r, c);
        }
        // Hint follow-up:
        //   • Hint satisfied by this move → clear the whole hint.
        //   • ♛ changed but hint not satisfied → still clear, since
        //     the underlying solver state has moved and the hint's
        //     highlighted cells are stale.
        //   • × toggle that leaves the hint unsatisfied → leave the
        //     overlay untouched. The stripes stay put until the last
        //     violation is handled and the auto-clear kicks in.
        // When we clear mid-drag we also cancel dragState so the
        // player's finger doesn't keep painting extra × marks onto
        // unrelated cells after the hint disappears.
        if (state.hint && (isHintSatisfied() || queenInvolved)) {
            clearHint();
            if (dragState) dragState = null;
        }
        repaintSymbols();
        updateStatusRow();
    }

    // Is (r,c) part of the current hint? Used both to gate applyCellState
    // during a hint (only hint cells are interactive) and to know which
    // cells to leave un-dimmed in the overlay. Returns true when no hint
    // is active so the freeze predicate falls open by default.
    function isHintCell(r, c) {
        const h = state.hint;
        if (!h) return true;
        const inList = (cells) => {
            if (!cells) return false;
            for (const [hr, hc] of cells) {
                if (hr === r && hc === c) return true;
            }
            return false;
        };
        return inList(h.targetCells)
            || inList(h.violationCells)
            || inList(h.contextCells);
    }

    // Has the player fulfilled the currently-shown hint?
    //   error mode  — the player's board no longer disagrees with the
    //                 unique solution (all wrong ♛ / × have been fixed).
    //   T2 (target) — the target cell now holds ♛. Handled implicitly
    //                 via the queen-involved auto-clear path but we
    //                 still check here so the branch is uniform.
    //   T1/T3/T4/T5 — every violation cell now bears ×.
    //   noHint      — never "satisfied"; the banner stays until the
    //                 player toggles the button off.
    function isHintSatisfied() {
        const h = state.hint;
        if (!h || h.mode === 'noHint') return false;
        if (h.mode === 'error') {
            return findWrongPlacements().length === 0;
        }
        // T2 completion is "place ♛ at target" — even though we also
        // paint the group's other cells as stripes for the visual
        // "其他所有格子都被排除了", the semantically-meaningful action
        // is still the queen placement, so we don't clear the hint
        // just because the player rubber-stamped the strikes.
        if (h.tier === 'T2') {
            const t = h.targetCells && h.targetCells[0];
            return !!t && state.placements[t[0]][t[1]] === STATES.QUEEN;
        }
        // T1 kills + T3 / T4 / T5 covering — completion is "every
        // violation cell now bears ×".
        const violations = h.violationCells || [];
        if (violations.length === 0) return false;
        for (const [r, c] of violations) {
            if (state.placements[r][c] !== STATES.MARK) return false;
        }
        return true;
    }

    function cycleCell(r, c) {
        if (!state.puzzle || state.won) return;
        const cur = state.placements[r][c];
        const idx = STATE_CYCLE.indexOf(cur);
        const next = STATE_CYCLE[(idx + 1) % STATE_CYCLE.length];
        applyCellState(r, c, next);
    }

    // Map a pointer event to a board cell using the SVG viewBox math.
    // Mirrors Zip's helper: the playable area occupies viewBox coords
    // (0..BOARD_SIZE, 0..BOARD_SIZE) inside a 486×486 SVG with 3px
    // padding on each side.
    function eventToCell(ev) {
        if (!state.puzzle) return null;
        const N = state.puzzle.size;
        const rect = board.getBoundingClientRect();
        if (rect.width === 0 || rect.height === 0) return null;
        const vbx = (ev.clientX - rect.left) / rect.width * 486 - 3;
        const vby = (ev.clientY - rect.top) / rect.height * 486 - 3;
        if (vbx < 0 || vbx >= BOARD_SIZE) return null;
        if (vby < 0 || vby >= BOARD_SIZE) return null;
        const cs = BOARD_SIZE / N;
        return [Math.floor(vby / cs), Math.floor(vbx / cs)];
    }

    function onPointerDown(ev) {
        if (!state.puzzle || state.won) return;
        if (ev.button !== undefined && ev.button !== 0) return;
        if (dragState) return; // ignore secondary pointers mid-gesture
        const cell = eventToCell(ev);
        if (!cell) return;
        const [r, c] = cell;
        const cur = state.placements[r][c];

        ev.preventDefault();
        try { board.setPointerCapture(ev.pointerId); } catch (_) { /* ignore */ }

        let mode;
        if (cur === STATES.EMPTY) {
            // Tap-on-empty is already "→ ×" per the cycle, so we can
            // apply immediately and keep painting subsequent cells.
            applyCellState(r, c, STATES.MARK);
            mode = 'mark';
        } else if (cur === STATES.MARK) {
            // Ambiguous — could be a tap wanting × → ♛, or a drag
            // wanting to erase ×s. Defer until the pointer leaves this
            // cell; see the promotion logic in onPointerMove.
            mode = 'unmark-pending';
        } else {
            // Started on ♛ — behave like a click (cycle only if the
            // release lands here).
            mode = 'tap';
        }
        dragState = {
            pointerId: ev.pointerId, mode,
            startR: r, startC: c, lastR: r, lastC: c,
        };
    }

    function onPointerMove(ev) {
        if (!dragState || ev.pointerId !== dragState.pointerId) return;
        const cell = eventToCell(ev);
        if (!cell) return;
        const [r, c] = cell;
        if (r === dragState.lastR && c === dragState.lastC) return;
        dragState.lastR = r; dragState.lastC = c;

        // First move away from the start commits an unmark-pending
        // gesture into a real drag-erase: clear the starting × and
        // switch modes so the current cell (and subsequent ones) all
        // go through the same rule.
        if (dragState.mode === 'unmark-pending') {
            applyCellState(dragState.startR, dragState.startC, STATES.EMPTY);
            dragState.mode = 'unmark';
        }

        if (dragState.mode === 'mark'
            && state.placements[r][c] === STATES.EMPTY) {
            applyCellState(r, c, STATES.MARK);
        } else if (dragState.mode === 'unmark'
            && state.placements[r][c] === STATES.MARK) {
            applyCellState(r, c, STATES.EMPTY);
        }
    }

    function onPointerUp(ev) {
        if (!dragState || ev.pointerId !== dragState.pointerId) return;
        const cell = eventToCell(ev);
        const { mode, startR, startC, pointerId } = dragState;
        dragState = null;
        try { board.releasePointerCapture(pointerId); } catch (_) { /* ignore */ }
        // 'tap' (started on ♛) and 'unmark-pending' (started on × but
        // never left) both resolve as a plain cycle if the release
        // lands on the starting cell. Everything else has already been
        // committed by the move handler.
        const tapLike = mode === 'tap' || mode === 'unmark-pending';
        if (tapLike
            && cell && cell[0] === startR && cell[1] === startC) {
            cycleCell(startR, startC);
        }
    }

    // -----------------------------------------------------------------
    // Hint
    //
    // The active hint mirrors Tango's shape closely (single source of
    // banner + overlay state) so tweaks to the hint UI in future can
    // stay symmetric across games.
    //
    // state.hint shape when active:
    //   {
    //     mode:           'error' | 'deduction' | 'noHint',
    //     textKey:        i18n key for the banner sentence,
    //     argKey?:        i18n key for a localised noun to splice in
    //                     ("row" / "column" / "region"); resolved at
    //                     render time so a locale flip refreshes it,
    //     textArgRaw?:    numeric arg used by error-mode banners (the
    //                     count of wrong ♛s),
    //     targetCells:    [[r,c], ...] — darker amber tint (the
    //                     placement in T2, or the T5 region-killer
    //                     candidates),
    //     contextCells:   [[r,c], ...] — light amber tint (candidates
    //                     inside the target group),
    //     violationCells: [[r,c], ...] — striped red overlay (cells
    //                     the deduction rules out, or the wrong ♛s
    //                     in error mode).
    //   }
    // -----------------------------------------------------------------

    // Build a solver state pre-populated with the player's progress.
    //   • Correctly-placed ♛ go through placeAt so T1 kills cascade
    //     into the candidate grid.
    //   • × marks the player has laid down also get excluded — this
    //     matters because deduction steps (T2 / T4 / T3 / T5) are
    //     computed from scratch each hint click and, without this,
    //     the solver would keep re-suggesting the same excludedAt set
    //     the player already handled.
    // Wrong placements are handled by findWrongPlacements and short-
    // circuit the hint before we get here.
    function composeSolverStateForHint() {
        const S = window.PuzzleSolvers && window.PuzzleSolvers.queens;
        if (!S || typeof S.placeAt !== 'function'
            || typeof S.makeSolverState !== 'function'
            || typeof S.excludeAt !== 'function') {
            console.warn(
                '[queens] Solver missing expected exports — hard-refresh '
                + 'the page (Ctrl+F5) to pick up js/generators/queens.js.');
            return null;
        }
        const st = S.makeSolverState(state.puzzle.regions, state.puzzle.size);
        const N = state.puzzle.size;
        const sol = state.puzzle.solution;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.placements[r][c] !== STATES.QUEEN) continue;
                if (sol[r] !== c) continue;   // wrong ♛ — ignore
                S.placeAt(st, r, c);
            }
        }
        // Applied AFTER placeAt so × on cells already killed by a ♛ is
        // just a harmless no-op (candidate was already false).
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.placements[r][c] === STATES.MARK) {
                    S.excludeAt(st, r, c);
                }
            }
        }
        return st;
    }

    // Return the first correctly-placed queen whose "kills" (same row,
    // column, region, or 8-neighbourhood) contain at least one cell
    // the player hasn't marked with × yet, along with those unmarked
    // kill cells. This is the T1 hint — the first thing a player is
    // supposed to do after placing a queen. Iteration is row-major so
    // repeated hint clicks walk deterministically through the board.
    function findUnmarkedKills() {
        if (!state.puzzle) return null;
        const N = state.puzzle.size;
        const sol = state.puzzle.solution;
        const regions = state.puzzle.regions;
        for (let qr = 0; qr < N; qr++) {
            for (let qc = 0; qc < N; qc++) {
                if (state.placements[qr][qc] !== STATES.QUEEN) continue;
                if (sol[qr] !== qc) continue;   // wrong ♛ — ignored
                const kills = [];
                for (let r = 0; r < N; r++) {
                    for (let c = 0; c < N; c++) {
                        if (r === qr && c === qc) continue;
                        if (state.placements[r][c] !== STATES.EMPTY) continue;
                        const sameRow = r === qr;
                        const sameCol = c === qc;
                        const adj = Math.abs(r - qr) <= 1
                            && Math.abs(c - qc) <= 1;
                        const sameRegion =
                            regions[r][c] === regions[qr][qc];
                        if (sameRow || sameCol || adj || sameRegion) {
                            kills.push([r, c]);
                        }
                    }
                }
                if (kills.length) return { queen: [qr, qc], kills };
            }
        }
        return null;
    }

    // A placement is "wrong" if it provably disagrees with the puzzle's
    // unique solution:
    //   • ♛ on a cell that isn't the solution's queen column for that
    //     row (subsumes row / adjacency / region conflicts too — any
    //     of those means at least one queen must be off-solution), or
    //   • × on a cell that IS the solution's queen column for that
    //     row (the player ruled out the one place a queen must go).
    function findWrongPlacements() {
        const N = state.puzzle.size;
        const sol = state.puzzle.solution;
        const out = [];
        for (let r = 0; r < N; r++) {
            const solCol = sol[r];
            for (let c = 0; c < N; c++) {
                const s = state.placements[r][c];
                if (s === STATES.QUEEN && solCol !== c) {
                    out.push([r, c]);
                } else if (s === STATES.MARK && solCol === c) {
                    out.push([r, c]);
                }
            }
        }
        return out;
    }

    // Convert a solver step into a hint entry (mode='deduction'). The
    // `argKey` is the i18n key for the {row/column/region} noun the
    // banner splices in; resolving it at render time (not now) lets a
    // mid-hint locale flip refresh the sentence.
    function stepToHint(step) {
        const kindKey = step.groupKind === 'row' ? 'queensHintKindRow'
            : step.groupKind === 'col' ? 'queensHintKindCol'
                : 'queensHintKindRegion';

        if (step.tier === 'T2') {
            // Only the placement cell stays bright — every other cell
            // in the row / column / region gets the stripe treatment
            // so the banner's "其他所有格子都被排除了" reads visually.
            const [tr, tc] = step.placedAt;
            const others = (step.groupCells || []).filter(
                ([r, c]) => !(r === tr && c === tc),
            );
            return {
                mode: 'deduction',
                tier: 'T2',
                textKey: 'queensHintT2',
                argKey: kindKey,
                targetCells: [step.placedAt],
                contextCells: [],
                violationCells: others,
            };
        }
        if (step.tier === 'T3') {
            return {
                mode: 'deduction',
                tier: 'T3',
                textKey: 'queensHintT3',
                argKey: step.axis === 'row'
                    ? 'queensHintKindRow' : 'queensHintKindCol',
                targetCells: [],
                contextCells: step.regionCandidates || [],
                violationCells: step.excludedAt || [],
            };
        }
        // T4 / T5 — covering. Treat the T5 region-killer subset as
        // additional target cells so the player can spot which
        // candidates specifically rely on the region-colour framing.
        return {
            mode: 'deduction',
            tier: step.tier,
            textKey: 'queensHintCover',
            argKey: kindKey,
            targetCells: step.regionKillers || [],
            contextCells: step.groupCandidates || [],
            violationCells: step.excludedAt || [],
        };
    }

    // Run one solver step at the priority the main solver uses:
    // T2 → T4 → T3 → T5. Higher-tier deductions are always available
    // to the hint system regardless of difficulty — a player asking
    // for help gets the easiest currently-applicable reasoning even
    // if the puzzle was tagged "easy".
    function computeDeductionHint() {
        const S = window.PuzzleSolvers && window.PuzzleSolvers.queens;
        const st = composeSolverStateForHint();
        if (!st || !S) return null;
        return S.stepT2(st) || S.stepT4(st) || S.stepT3(st) || S.stepT5(st);
    }

    function showHint() {
        if (!state.puzzle || state.won) return;
        if (state.hint) { clearHint(); return; }

        // Priority 1: any ♛ that disagrees with the unique solution.
        // Fixing those has to come before any further deduction —
        // running the solver from a wrong state would either spin or
        // give misleading advice.
        const wrong = findWrongPlacements();
        if (wrong.length > 0) {
            state.hint = {
                mode: 'error',
                textKey: wrong.length === 1
                    ? 'queensHintWrongOne' : 'queensHintWrongMany',
                textArgRaw: wrong.length,   // literal arg for i18n(count)
                // Error highlighting is dim-based: the wrong cells stay
                // bright while the rest of the board fades. No stripes
                // — the banner explicitly says these cells are "醒目
                // 標示 (highlighted)", so the spotlight IS the signal.
                targetCells: [],
                contextCells: wrong,
                violationCells: [],
            };
            renderHintBanner();
            repaintHintOverlay();
            return;
        }

        // Priority 2: T1 kills — remind the player to mark the row /
        // column / region / adjacent cells of a correctly-placed ♛
        // before we go looking for subtler deductions. This mirrors
        // LinkedIn's first-line-of-defence hint.
        const kills = findUnmarkedKills();
        if (kills) {
            state.hint = {
                mode: 'kills',
                textKey: 'queensHintT1',
                // Highlight the dominating ♛ as the target so it gets the
                // amber-fill + orange-outline treatment — the sentence
                // "此♛把..." then visually points at exactly which queen
                // it means, even if the player has several on the board.
                targetCells: [kills.queen],
                contextCells: [],
                violationCells: kills.kills,
            };
            renderHintBanner();
            repaintHintOverlay();
            return;
        }

        const step = computeDeductionHint();
        state.hint = step ? stepToHint(step) : {
            mode: 'noHint',
            textKey: 'queensHintNoAvail',
            targetCells: [], contextCells: [], violationCells: [],
        };
        renderHintBanner();
        repaintHintOverlay();
    }

    function clearHint() {
        if (!state.hint) return;
        state.hint = null;
        renderHintBanner();
        repaintHintOverlay();
    }

    function renderHintBanner() {
        const banner = state.hintBanner;
        if (!banner) return;
        const h = state.hint;
        if (!h) {
            banner.hidden = true;
            banner.textContent = '';
            banner.classList.remove('error');
            return;
        }
        // Deduction hints splice in a localised noun ("row" / "column"
        // / "region"); error hints splice in a raw integer. Both go
        // through PC.i18n.t so string or function entries work.
        const arg = h.argKey ? PC.i18n.t(h.argKey)
            : (h.textArgRaw != null ? h.textArgRaw : undefined);
        banner.textContent = arg !== undefined
            ? PC.i18n.t(h.textKey, arg)
            : PC.i18n.t(h.textKey);
        banner.classList.toggle('error', h.mode === 'error');
        banner.hidden = false;
    }

    function repaintHintOverlay() {
        if (!board) return;
        const fillGroup = board.querySelector('#hint-fill');
        const outlineGroup = board.querySelector('#hint-outline');
        const dimGroup = board.querySelector('#hint-dim');
        if (!fillGroup || !outlineGroup || !dimGroup) return;
        while (fillGroup.firstChild) fillGroup.removeChild(fillGroup.firstChild);
        while (outlineGroup.firstChild) {
            outlineGroup.removeChild(outlineGroup.firstChild);
        }
        while (dimGroup.firstChild) dimGroup.removeChild(dimGroup.firstChild);
        const h = state.hint;
        if (!h) return;

        const N = state.puzzle.size;

        // The design emphasis is "spotlight the hint, dim everything
        // else". Non-hint cells are dimmed below; the hint cells wear
        // only the minimum decoration they need to distinguish role:
        //   contextCells / targetCells — no decoration. Their region
        //     colour is enough once the surroundings fade back, and
        //     the ♛ / × / empty content already tells the player
        //     which cell is which.
        //   violationCells — diagonal stripes drawn in a darkened
        //     shade of the cell's own region colour, so the "excluded"
        //     signal reads clearly without introducing an out-of-
        //     palette red.
        const regions = state.puzzle.regions;
        for (const [r, c] of h.violationCells || []) {
            const { x, y, size } = cellRect(N, r, c);
            const k = regions[r][c] % REGION_COLORS.length;
            fillGroup.appendChild(PC.svgEl('rect', {
                x, y, width: size, height: size,
                fill: `url(#queens-hint-stripes-${k})`,
            }));
        }

        // Dim overlay on every non-hint cell. Painted above the symbol
        // layer so ♛ / × marks on dimmed cells also fade — that's what
        // makes the highlighted cells visually "pop" without any extra
        // decoration on them.
        const hintSet = new Set();
        const collect = (cells) => {
            for (const [r, c] of cells || []) hintSet.add(r * N + c);
        };
        collect(h.contextCells);
        collect(h.targetCells);
        collect(h.violationCells);
        if (hintSet.size === 0) return;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (hintSet.has(r * N + c)) continue;
                const { x, y, size } = cellRect(N, r, c);
                dimGroup.appendChild(PC.svgEl('rect', {
                    x, y, width: size, height: size,
                    fill: '#000',
                    'fill-opacity': 0.55,
                    'pointer-events': 'none',
                }));
            }
        }
    }

    // URL share state — same pattern as Tango. `urlInitial` is
    // captured at module load, so a friend who opens a shared link
    // arrives here with the requested puzzle. We hand the seed to
    // startNewGame *once*; subsequent New Game clicks roll a fresh
    // seed and the address bar re-syncs to whatever just generated.
    const VALID_SIZES = new Set([5, 6, 7, 8, 9, 10, 11, 12]);
    const VALID_DIFFS = new Set(['easy', 'medium', 'hard']);

    function readUrlInitial() {
        if (!PC.share) return null;
        const raw = PC.share.readParams();
        if (!VALID_SIZES.has(raw.size)) return null;
        if (!VALID_DIFFS.has(raw.difficulty)) return null;
        if (!Number.isInteger(raw.seed)) return null;
        return { size: raw.size, difficulty: raw.difficulty, seed: raw.seed };
    }

    const urlInitial = readUrlInitial();
    let pendingSeed = urlInitial ? urlInitial.seed : null;

    async function startNewGame() {
        const seed = pendingSeed != null
            ? pendingSeed
            : ((Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0);
        pendingSeed = null;
        state.puzzle = await generatePuzzle(shell.size, shell.difficulty, seed);
        ensurePlacementsForCurrent();
        clearHint();
        renderBoard();
        updateStatusRow();
        if (PC.share) {
            PC.share.replaceUrl({
                size: shell.size,
                difficulty: shell.difficulty,
                seed,
            });
        }
    }

    async function onShareClick() {
        if (!PC.share) return;
        const ok = await PC.share.copyCurrentUrl();
        if (PC.toast) {
            PC.toast.show(PC.i18n.t(ok ? 'shareCopied' : 'shareFailed'));
        }
    }

    function resetPlacements() {
        if (!state.puzzle) return;
        ensurePlacementsForCurrent();
        state.won = false;
        clearHint();
        repaintSymbols();
        updateStatusRow();
    }

    // -----------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------

    function init() {
        shell = PC.shell.create({
            gameId: 'queens',
            difficulty: {
                default: urlInitial ? urlInitial.difficulty : 'medium',
            },
            size: {
                kind: 'slider', min: 5, max: 12,
                default: urlInitial ? urlInitial.size : 8,
            },
            onNewGame: startNewGame,
            onReset: resetPlacements,
            onReveal: repaintSymbols,
        });
        board = shell.dom.board;
        board.classList.add('drag-board');
        board.addEventListener('pointerdown', onPointerDown);
        board.addEventListener('pointermove', onPointerMove);
        board.addEventListener('pointerup', onPointerUp);
        board.addEventListener('pointercancel', onPointerUp);
        board.addEventListener('contextmenu', (ev) => ev.preventDefault());

        state.hintBanner = document.getElementById('hint-banner');
        state.hintButton = document.getElementById('hint-btn');
        if (state.hintButton) {
            state.hintButton.addEventListener('click', showHint);
        }

        const shareBtn = document.getElementById('share-btn');
        if (shareBtn) {
            shareBtn.addEventListener('click', onShareClick);
        }
        // Rerender the banner if the player flips the locale mid-hint,
        // so a T4 / T3 / etc. explanation picks up the new language
        // without needing to re-request the hint.
        if (PC.i18n && typeof PC.i18n.subscribe === 'function') {
            PC.i18n.subscribe(() => { if (state.hint) renderHintBanner(); });
        }

        shell.start();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
