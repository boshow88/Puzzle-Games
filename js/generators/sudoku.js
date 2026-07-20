/**
 * Sudoku generator — full-solution + logic-bounded hole-digging.
 *
 * Strategy (mirrors Tango / Queens in spirit: build a solution, then
 * carve it down under a solver that only uses the difficulty's allowed
 * techniques, so the delivered puzzle is guaranteed uniquely solvable
 * by exactly those techniques):
 *
 *   1. Generate a random complete solution via randomised row/col/box
 *      backtracking.
 *   2. Copy it to the clue grid, then visit cells in random order and
 *      try to blank each one. After blanking, run the technique-bounded
 *      solver from the current clue grid: if it still solves the board
 *      completely, the blank is safe (uniqueness preserved) and we keep
 *      it; otherwise we restore the clue.
 *   3. Difficulty controls how far we dig (minimum clue count to keep).
 *      hard digs as far as the technique set allows.
 *
 * Why "solves completely ⇒ unique": every technique here only ever
 * places a *forced* digit (a cell with a single candidate, or a digit
 * with a single home in a unit). A chain of forced moves that fills the
 * grid proves the solution is the only one reachable — hence unique.
 *
 * Techniques (basic singles for now; hard will gain advanced ones later):
 *   - fullHouse    : a unit (row/col/box) with exactly one empty cell.
 *   - nakedSingle  : a cell whose row+col+box leave exactly one digit.
 *   - hiddenSingle : a digit that fits exactly one cell of a unit.
 *
 * Puzzle JSON contract (unchanged from the old inline generator):
 *   { id, game:'sudoku', size:N, difficulty, boxRows, boxCols,
 *     prefilled:int[N][N] (0 empty / 1..N clue), solution:int[N][N],
 *     stats:{ clues, techniqueCounts } }
 */
(function (global) {
    'use strict';

    const PC = global.PuzzleCommon;

    /** Box dimensions per board size (rows × cols of a single box). */
    const BOX_SHAPE = {
        6: { rows: 2, cols: 3 },
        9: { rows: 3, cols: 3 },
    };

    // Techniques allowed per difficulty. Each tier is a strict superset
    // of the previous one. All techniques are pattern-based (a human can
    // spot them by eye) — no trial-and-error / contradiction chains.
    //   easy   — basic singles only.
    //   medium — + locked candidates (box↔line) and naked/hidden pairs.
    //   hard   — + naked/hidden triples, X-Wing, XY-Wing.
    // A stronger technique set lets the digger remove more clues while
    // keeping the puzzle uniquely solvable by exactly those techniques.
    const TECHNIQUES_BY_DIFFICULTY = {
        easy: {
            fullHouse: true, nakedSingle: true, hiddenSingle: true,
        },
        medium: {
            fullHouse: true, nakedSingle: true, hiddenSingle: true,
            lockedCandidates: true, nakedPair: true, hiddenPair: true,
        },
        hard: {
            fullHouse: true, nakedSingle: true, hiddenSingle: true,
            lockedCandidates: true, nakedPair: true, hiddenPair: true,
            nakedTriple: true, hiddenTriple: true, xWing: true, xyWing: true,
        },
    };

    // Minimum clue count to keep when digging. Lower = harder (fewer
    // givens, more scanning). 0 means "dig as far as the technique set
    // allows" — used by hard so it bottoms out at the singles limit.
    function minClues(N, difficulty) {
        if (N === 6) {
            if (difficulty === 'easy') return 20;
            if (difficulty === 'medium') return 14;
            return 0;
        }
        // 9×9
        if (difficulty === 'easy') return 36;
        if (difficulty === 'medium') return 30;
        return 0;
    }

    function boxDims(N) { return BOX_SHAPE[N] || BOX_SHAPE[9]; }

    function popcount(x) {
        let n = 0;
        while (x) { n += x & 1; x >>>= 1; }
        return n;
    }

    // Digit (1..N) of a mask known to hold exactly one bit.
    function bitToDigit(mask) {
        let d = 1;
        while (mask > 1) { mask >>>= 1; d += 1; }
        return d;
    }

    // -----------------------------------------------------------------
    // Full solution — randomised backtracking with row/col/box masks.
    // -----------------------------------------------------------------

    function placeValidGrid(N, boxRows, boxCols, rng) {
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        const rowMask = new Array(N).fill(0);
        const colMask = new Array(N).fill(0);
        const boxMask = new Array(N).fill(0);
        const boxesPerRow = Math.floor(N / boxCols);

        function boxIndex(r, c) {
            return Math.floor(r / boxRows) * boxesPerRow + Math.floor(c / boxCols);
        }
        function bit(d) { return 1 << (d - 1); }

        function digitsForCell(r, c) {
            const used = rowMask[r] | colMask[c] | boxMask[boxIndex(r, c)];
            const out = [];
            for (let d = 1; d <= N; d++) {
                if ((used & bit(d)) === 0) out.push(d);
            }
            return PC.rng.shuffle(out, rng);
        }

        function solve(idx) {
            if (idx === N * N) return true;
            const r = Math.floor(idx / N);
            const c = idx % N;
            const b = boxIndex(r, c);
            for (const d of digitsForCell(r, c)) {
                grid[r][c] = d;
                const m = bit(d);
                rowMask[r] |= m; colMask[c] |= m; boxMask[b] |= m;
                if (solve(idx + 1)) return true;
                grid[r][c] = 0;
                rowMask[r] &= ~m; colMask[c] &= ~m; boxMask[b] &= ~m;
            }
            return false;
        }

        return solve(0) ? grid : null;
    }

    /** Trivially valid grid (rotated row scheme) — last-ditch fallback. */
    function fallbackGrid(N, boxRows, boxCols) {
        const grid = Array.from({ length: N }, () => new Array(N).fill(0));
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                grid[r][c] = ((boxCols * (r % boxRows)
                    + Math.floor(r / boxRows) + c) % N) + 1;
            }
        }
        return grid;
    }

    // -----------------------------------------------------------------
    // Solver state — the grid plus incremental row/col/box usage masks
    // and precomputed unit cell lists. `grid` is a private copy so the
    // caller's array is never mutated.
    // -----------------------------------------------------------------

    function makeState(grid, N, boxRows, boxCols) {
        const boxesPerRow = Math.floor(N / boxCols);
        const g = grid.map((row) => row.slice());
        const rowMask = new Array(N).fill(0);
        const colMask = new Array(N).fill(0);
        const boxMask = new Array(N).fill(0);
        let filled = 0;

        const boxIndex = (r, c) =>
            Math.floor(r / boxRows) * boxesPerRow + Math.floor(c / boxCols);

        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                const d = g[r][c];
                if (d !== 0) {
                    const m = 1 << (d - 1);
                    rowMask[r] |= m; colMask[c] |= m; boxMask[boxIndex(r, c)] |= m;
                    filled += 1;
                }
            }
        }

        const fullMask = (1 << N) - 1;
        // Persistent candidate bitmask per cell (0 for filled cells).
        // Advanced techniques work by removing bits here; the singles
        // read whatever remains.
        const cands = Array.from({ length: N }, () => new Array(N).fill(0));
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (g[r][c] !== 0) continue;
                cands[r][c] = fullMask
                    & ~(rowMask[r] | colMask[c] | boxMask[boxIndex(r, c)]);
            }
        }

        // Precompute the cell list of every unit once. Units are indexed
        // 0..N-1 for rows, cols, boxes independently.
        const rows = Array.from({ length: N }, () => []);
        const cols = Array.from({ length: N }, () => []);
        const boxes = Array.from({ length: N }, () => []);
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                rows[r].push([r, c]);
                cols[c].push([r, c]);
                boxes[boxIndex(r, c)].push([r, c]);
            }
        }

        return {
            N, boxRows, boxCols, boxIndex,
            grid: g, cands, rowMask, colMask, boxMask, filled,
            rows, cols, boxes, fullMask,
        };
    }

    // Place digit d at (r,c): update grid + masks, clear the cell's own
    // candidates, and strike d from every peer's candidates. Returns
    // true if it actually filled an empty cell.
    function place(state, r, c, d) {
        if (state.grid[r][c] !== 0) return false;
        const { N } = state;
        const m = 1 << (d - 1);
        const b = state.boxIndex(r, c);
        state.grid[r][c] = d;
        state.rowMask[r] |= m;
        state.colMask[c] |= m;
        state.boxMask[b] |= m;
        state.cands[r][c] = 0;
        state.filled += 1;
        const clear = ~m;
        for (let i = 0; i < N; i++) {
            if (state.grid[r][i] === 0) state.cands[r][i] &= clear;
            if (state.grid[i][c] === 0) state.cands[i][c] &= clear;
        }
        for (const [br, bc] of state.boxes[b]) {
            if (state.grid[br][bc] === 0) state.cands[br][bc] &= clear;
        }
        return true;
    }

    // Remove digit d from (r,c)'s candidates. Returns true if it was
    // present (real progress).
    function eliminate(state, r, c, d) {
        const m = 1 << (d - 1);
        if ((state.cands[r][c] & m) === 0) return false;
        state.cands[r][c] &= ~m;
        return true;
    }

    // Candidate bitmask of a cell (0 if filled).
    function candMask(state, r, c) { return state.cands[r][c]; }

    // -----------------------------------------------------------------
    // Step model. Every technique returns a step, or null. A step is:
    //   { technique,
    //     placements:  [{r,c,value}],   // 0+ cells to fill (singles: 1)
    //     eliminations:[{r,c,d}],       // 0+ candidate removals (advanced)
    //     cells:       [[r,c],...],     // the pattern cells to spotlight
    //     digits:      [d,...],         // the digit(s) the technique is about
    //     unit:        {kind,index}|null }
    // Singles use `placements`; every other technique uses `eliminations`.
    // -----------------------------------------------------------------

    function placementStep(technique, r, c, value, unit) {
        return {
            technique,
            placements: [{ r, c, value }],
            eliminations: [],
            cells: [[r, c]],
            digits: [value],
            unit: unit || null,
        };
    }

    function elimStep(technique, eliminations, cells, digits, unit) {
        return {
            technique,
            placements: [],
            eliminations,
            cells,
            digits,
            unit: unit || null,
        };
    }

    // Digits (1..N) present in a bitmask.
    function bitsOf(mask) {
        const out = [];
        let d = 1;
        while (mask) {
            if (mask & 1) out.push(d);
            mask >>>= 1; d += 1;
        }
        return out;
    }

    // All k-combinations of arr (k small, arr short → cheap).
    function combinations(arr, k) {
        const res = [];
        const combo = [];
        (function rec(start) {
            if (combo.length === k) { res.push(combo.slice()); return; }
            for (let i = start; i <= arr.length - (k - combo.length); i++) {
                combo.push(arr[i]);
                rec(i + 1);
                combo.pop();
            }
        })(0);
        return res;
    }

    function unitList(state) {
        const out = [];
        for (let i = 0; i < state.N; i++) {
            out.push({ kind: 'row', index: i, cells: state.rows[i] });
        }
        for (let i = 0; i < state.N; i++) {
            out.push({ kind: 'col', index: i, cells: state.cols[i] });
        }
        for (let i = 0; i < state.N; i++) {
            out.push({ kind: 'box', index: i, cells: state.boxes[i] });
        }
        return out;
    }

    // ---- Singles ----

    function findFullHouse(state) {
        const { N } = state;
        const kinds = [
            ['row', state.rows], ['col', state.cols], ['box', state.boxes],
        ];
        for (const [kind, units] of kinds) {
            for (let u = 0; u < N; u++) {
                const cells = units[u];
                let emptyCell = null;
                let emptyCount = 0;
                let present = 0;
                for (const [r, c] of cells) {
                    const d = state.grid[r][c];
                    if (d === 0) { emptyCell = [r, c]; emptyCount += 1; }
                    else present |= 1 << (d - 1);
                }
                if (emptyCount !== 1) continue;
                const missing = state.fullMask & ~present;
                if (popcount(missing) !== 1) continue; // defensive
                return placementStep('fullHouse', emptyCell[0], emptyCell[1],
                    bitToDigit(missing), { kind, index: u });
            }
        }
        return null;
    }

    function findNakedSingle(state) {
        const { N } = state;
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.grid[r][c] !== 0) continue;
                const cm = state.cands[r][c];
                if (popcount(cm) === 1) {
                    return placementStep('nakedSingle', r, c,
                        bitToDigit(cm), null);
                }
            }
        }
        return null;
    }

    function findHiddenSingle(state) {
        const { N } = state;
        const kinds = [
            ['row', state.rows], ['col', state.cols], ['box', state.boxes],
        ];
        for (const [kind, units] of kinds) {
            for (let u = 0; u < N; u++) {
                const cells = units[u];
                for (let d = 1; d <= N; d++) {
                    const bitD = 1 << (d - 1);
                    let homeCell = null;
                    let homes = 0;
                    let alreadyPlaced = false;
                    for (const [r, c] of cells) {
                        if (state.grid[r][c] === d) { alreadyPlaced = true; break; }
                        if (state.grid[r][c] !== 0) continue;
                        if (state.cands[r][c] & bitD) {
                            homeCell = [r, c]; homes += 1;
                            if (homes > 1) break;
                        }
                    }
                    if (alreadyPlaced || homes !== 1) continue;
                    return placementStep('hiddenSingle', homeCell[0], homeCell[1],
                        d, { kind, index: u });
                }
            }
        }
        return null;
    }

    // ---- Locked candidates ----

    // Empty cells of a unit that still hold digit d as a candidate;
    // returns null if d is already placed in the unit.
    function candidateHomes(state, cells, d) {
        const bitD = 1 << (d - 1);
        const homes = [];
        for (const [r, c] of cells) {
            if (state.grid[r][c] === d) return null;
            if (state.grid[r][c] === 0 && (state.cands[r][c] & bitD)) {
                homes.push([r, c]);
            }
        }
        return homes;
    }

    // Pointing: in a box, digit d confined to a single row/col ⇒ remove
    // d from the rest of that row/col.
    function findLockedPointing(state) {
        const { N } = state;
        for (let b = 0; b < N; b++) {
            for (let d = 1; d <= N; d++) {
                const homes = candidateHomes(state, state.boxes[b], d);
                if (!homes || homes.length < 2) continue;
                const sameRow = homes.every(([r]) => r === homes[0][0]);
                const sameCol = homes.every(([, c]) => c === homes[0][1]);
                if (sameRow) {
                    const rr = homes[0][0];
                    const elims = [];
                    for (let c = 0; c < N; c++) {
                        if (state.boxIndex(rr, c) === b) continue;
                        if (state.grid[rr][c] === 0
                            && (state.cands[rr][c] & (1 << (d - 1)))) {
                            elims.push({ r: rr, c, d });
                        }
                    }
                    if (elims.length) {
                        return elimStep('lockedPointing', elims, homes.slice(),
                            [d], { kind: 'box', index: b });
                    }
                }
                if (sameCol) {
                    const cc = homes[0][1];
                    const elims = [];
                    for (let r = 0; r < N; r++) {
                        if (state.boxIndex(r, cc) === b) continue;
                        if (state.grid[r][cc] === 0
                            && (state.cands[r][cc] & (1 << (d - 1)))) {
                            elims.push({ r, c: cc, d });
                        }
                    }
                    if (elims.length) {
                        return elimStep('lockedPointing', elims, homes.slice(),
                            [d], { kind: 'box', index: b });
                    }
                }
            }
        }
        return null;
    }

    // Claiming: in a row/col, digit d confined to a single box ⇒ remove
    // d from the rest of that box.
    function findLockedClaiming(state) {
        const { N } = state;
        const scan = (units, kind) => {
            for (let u = 0; u < N; u++) {
                for (let d = 1; d <= N; d++) {
                    const homes = candidateHomes(state, units[u], d);
                    if (!homes || homes.length < 2) continue;
                    const b0 = state.boxIndex(homes[0][0], homes[0][1]);
                    if (!homes.every(([r, c]) => state.boxIndex(r, c) === b0)) {
                        continue;
                    }
                    const elims = [];
                    for (const [br, bc] of state.boxes[b0]) {
                        const inUnit = kind === 'row' ? br === u : bc === u;
                        if (inUnit) continue;
                        if (state.grid[br][bc] === 0
                            && (state.cands[br][bc] & (1 << (d - 1)))) {
                            elims.push({ r: br, c: bc, d });
                        }
                    }
                    if (elims.length) {
                        return elimStep('lockedClaiming', elims, homes.slice(),
                            [d], { kind, index: u });
                    }
                }
            }
            return null;
        };
        return scan(state.rows, 'row') || scan(state.cols, 'col');
    }

    // ---- Naked / hidden subsets ----

    function findNakedSubset(state, k, technique) {
        const { N } = state;
        for (const unit of unitList(state)) {
            const cand = unit.cells.filter(([r, c]) => {
                if (state.grid[r][c] !== 0) return false;
                const n = popcount(state.cands[r][c]);
                return n >= 2 && n <= k;
            });
            if (cand.length < k) continue;
            for (const group of combinations(cand, k)) {
                let union = 0;
                for (const [r, c] of group) union |= state.cands[r][c];
                if (popcount(union) !== k) continue;
                const inGroup = new Set(group.map(([r, c]) => r * N + c));
                const elims = [];
                for (const [r, c] of unit.cells) {
                    if (state.grid[r][c] !== 0 || inGroup.has(r * N + c)) continue;
                    const hit = state.cands[r][c] & union;
                    for (const d of bitsOf(hit)) elims.push({ r, c, d });
                }
                if (elims.length) {
                    return elimStep(technique, elims, group.slice(),
                        bitsOf(union), { kind: unit.kind, index: unit.index });
                }
            }
        }
        return null;
    }

    function findHiddenSubset(state, k, technique) {
        const { N } = state;
        for (const unit of unitList(state)) {
            const homesByDigit = {};
            const avail = [];
            for (let d = 1; d <= N; d++) {
                const homes = candidateHomes(state, unit.cells, d);
                if (!homes) continue; // already placed
                if (homes.length >= 2 && homes.length <= k) {
                    homesByDigit[d] = homes;
                    avail.push(d);
                }
            }
            if (avail.length < k) continue;
            for (const dgroup of combinations(avail, k)) {
                const cellKeys = new Set();
                for (const d of dgroup) {
                    for (const [r, c] of homesByDigit[d]) cellKeys.add(r * N + c);
                }
                if (cellKeys.size !== k) continue;
                let keep = 0;
                for (const d of dgroup) keep |= 1 << (d - 1);
                const elims = [];
                const groupCells = [];
                for (const key of cellKeys) {
                    const r = Math.floor(key / N);
                    const c = key % N;
                    groupCells.push([r, c]);
                    const extra = state.cands[r][c] & ~keep;
                    for (const d of bitsOf(extra)) elims.push({ r, c, d });
                }
                if (elims.length) {
                    return elimStep(technique, elims, groupCells,
                        dgroup.slice(), { kind: unit.kind, index: unit.index });
                }
            }
        }
        return null;
    }

    // ---- X-Wing (single-digit 2×2 fish) ----

    function findXWing(state) {
        const { N } = state;
        for (let d = 1; d <= N; d++) {
            const bitD = 1 << (d - 1);
            // Rows whose d-candidates sit in exactly two columns.
            const rowCols = [];
            for (let r = 0; r < N; r++) {
                const homes = candidateHomes(state, state.rows[r], d);
                rowCols[r] = homes ? homes.map(([, c]) => c) : null;
            }
            for (let r1 = 0; r1 < N; r1++) {
                if (!rowCols[r1] || rowCols[r1].length !== 2) continue;
                for (let r2 = r1 + 1; r2 < N; r2++) {
                    if (!rowCols[r2] || rowCols[r2].length !== 2) continue;
                    if (rowCols[r1][0] !== rowCols[r2][0]
                        || rowCols[r1][1] !== rowCols[r2][1]) continue;
                    const [ca, cb] = rowCols[r1];
                    const elims = [];
                    for (let r = 0; r < N; r++) {
                        if (r === r1 || r === r2) continue;
                        for (const c of [ca, cb]) {
                            if (state.grid[r][c] === 0 && (state.cands[r][c] & bitD)) {
                                elims.push({ r, c, d });
                            }
                        }
                    }
                    if (elims.length) {
                        const step = elimStep('xWing', elims,
                            [[r1, ca], [r1, cb], [r2, ca], [r2, cb]], [d], null);
                        step.fish = 'row'; // defined by two rows; clears columns
                        return step;
                    }
                }
            }
            // Columns whose d-candidates sit in exactly two rows.
            const colRows = [];
            for (let c = 0; c < N; c++) {
                const homes = candidateHomes(state, state.cols[c], d);
                colRows[c] = homes ? homes.map(([r]) => r) : null;
            }
            for (let c1 = 0; c1 < N; c1++) {
                if (!colRows[c1] || colRows[c1].length !== 2) continue;
                for (let c2 = c1 + 1; c2 < N; c2++) {
                    if (!colRows[c2] || colRows[c2].length !== 2) continue;
                    if (colRows[c1][0] !== colRows[c2][0]
                        || colRows[c1][1] !== colRows[c2][1]) continue;
                    const [ra, rb] = colRows[c1];
                    const elims = [];
                    for (let c = 0; c < N; c++) {
                        if (c === c1 || c === c2) continue;
                        for (const r of [ra, rb]) {
                            if (state.grid[r][c] === 0 && (state.cands[r][c] & bitD)) {
                                elims.push({ r, c, d });
                            }
                        }
                    }
                    if (elims.length) {
                        const step = elimStep('xWing', elims,
                            [[ra, c1], [rb, c1], [ra, c2], [rb, c2]], [d], null);
                        step.fish = 'col'; // defined by two columns; clears rows
                        return step;
                    }
                }
            }
        }
        return null;
    }

    // ---- XY-Wing ----

    function findXYWing(state) {
        const { N } = state;
        const sees = (r1, c1, r2, c2) =>
            !(r1 === r2 && c1 === c2)
            && (r1 === r2 || c1 === c2
                || state.boxIndex(r1, c1) === state.boxIndex(r2, c2));
        const bivalue = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                if (state.grid[r][c] === 0 && popcount(state.cands[r][c]) === 2) {
                    bivalue.push([r, c]);
                }
            }
        }
        for (const [pr, pc] of bivalue) {
            const pMask = state.cands[pr][pc];
            for (const [ar, ac] of bivalue) {
                if (ar === pr && ac === pc) continue;
                if (!sees(pr, pc, ar, ac)) continue;
                const aMask = state.cands[ar][ac];
                const shareA = aMask & pMask;
                const zA = aMask & ~pMask;
                if (popcount(shareA) !== 1 || popcount(zA) !== 1) continue;
                for (const [br, bc] of bivalue) {
                    if ((br === pr && bc === pc) || (br === ar && bc === ac)) continue;
                    if (!sees(pr, pc, br, bc)) continue;
                    const bMask = state.cands[br][bc];
                    const shareB = bMask & pMask;
                    if (popcount(shareB) !== 1 || shareB === shareA) continue;
                    const zB = bMask & ~pMask;
                    if (zB !== zA) continue; // the wing digit must match
                    const zDigit = bitToDigit(zA);
                    const elims = [];
                    for (let r = 0; r < N; r++) {
                        for (let c = 0; c < N; c++) {
                            if (state.grid[r][c] !== 0) continue;
                            if ((r === pr && c === pc) || (r === ar && c === ac)
                                || (r === br && c === bc)) continue;
                            if ((state.cands[r][c] & zA) === 0) continue;
                            if (sees(ar, ac, r, c) && sees(br, bc, r, c)) {
                                elims.push({ r, c, d: zDigit });
                            }
                        }
                    }
                    if (elims.length) {
                        return elimStep('xyWing', elims,
                            [[pr, pc], [ar, ac], [br, bc]], [zDigit], null);
                    }
                }
            }
        }
        return null;
    }

    // First applicable step, easiest technique first. The order defines
    // both the generator's solve path and which technique a hint shows.
    function nextStep(state, techniques) {
        const t = techniques || TECHNIQUES_BY_DIFFICULTY.hard;
        let s = null;
        if (t.fullHouse && (s = findFullHouse(state))) return s;
        if (t.nakedSingle && (s = findNakedSingle(state))) return s;
        if (t.hiddenSingle && (s = findHiddenSingle(state))) return s;
        if (t.lockedCandidates && (s = findLockedPointing(state))) return s;
        if (t.lockedCandidates && (s = findLockedClaiming(state))) return s;
        if (t.nakedPair && (s = findNakedSubset(state, 2, 'nakedPair'))) return s;
        if (t.hiddenPair && (s = findHiddenSubset(state, 2, 'hiddenPair'))) return s;
        if (t.nakedTriple && (s = findNakedSubset(state, 3, 'nakedTriple'))) return s;
        if (t.hiddenTriple && (s = findHiddenSubset(state, 3, 'hiddenTriple'))) return s;
        if (t.xWing && (s = findXWing(state))) return s;
        if (t.xyWing && (s = findXYWing(state))) return s;
        return null;
    }

    function applyStep(state, step) {
        let changed = false;
        for (const p of step.placements) {
            if (place(state, p.r, p.c, p.value)) changed = true;
        }
        for (const e of step.eliminations) {
            if (eliminate(state, e.r, e.c, e.d)) changed = true;
        }
        return changed;
    }

    // Solve as far as the allowed techniques reach. Returns
    // { solved, filled, grid, techniqueCounts }.
    function solveWithTechniques(grid, N, boxRows, boxCols, techniques) {
        const state = makeState(grid, N, boxRows, boxCols);
        const techniqueCounts = {};
        // Elimination steps don't fill a cell, so the loop can run more
        // than N² times; bound it by the total candidate count instead.
        const safety = N * N * N + N * N + 50;
        for (let i = 0; i < safety; i++) {
            const step = nextStep(state, techniques);
            if (!step) break;
            const changed = applyStep(state, step);
            techniqueCounts[step.technique] =
                (techniqueCounts[step.technique] || 0) + 1;
            if (!changed) break; // safety: a technique that made no progress
        }
        return {
            solved: state.filled === N * N,
            filled: state.filled,
            grid: state.grid,
            techniqueCounts,
        };
    }

    // -----------------------------------------------------------------
    // Contradiction finder — first unit that contains a duplicate digit.
    // Used by the in-game "you have too many X here" error hint. Reads
    // the caller's grid directly (no state needed).
    // Returns { unitKind, unitIndex, value, cells:[[r,c],...] } or null.
    // -----------------------------------------------------------------

    function findContradiction(grid, N, boxRows, boxCols) {
        const boxesPerRow = Math.floor(N / boxCols);
        const boxIndex = (r, c) =>
            Math.floor(r / boxRows) * boxesPerRow + Math.floor(c / boxCols);
        const units = [];
        for (let i = 0; i < N; i++) {
            units.push({ kind: 'row', index: i, cells: [] });
            units.push({ kind: 'col', index: i, cells: [] });
            units.push({ kind: 'box', index: i, cells: [] });
        }
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) {
                units[r * 3].cells.push([r, c]);
                units[c * 3 + 1].cells.push([r, c]);
                units[boxIndex(r, c) * 3 + 2].cells.push([r, c]);
            }
        }
        for (const unit of units) {
            const seen = new Map();
            for (const [r, c] of unit.cells) {
                const d = grid[r][c];
                if (d === 0) continue;
                if (!seen.has(d)) seen.set(d, []);
                seen.get(d).push([r, c]);
            }
            for (const [d, cells] of seen) {
                if (cells.length > 1) {
                    return {
                        unitKind: unit.kind, unitIndex: unit.index,
                        value: d, cells,
                    };
                }
            }
        }
        return null;
    }

    // -----------------------------------------------------------------
    // Hole-digging — carve the solution down while keeping it uniquely
    // solvable by the allowed techniques.
    // -----------------------------------------------------------------

    function digHoles(solution, N, boxRows, boxCols, techniques, keepMin, rng) {
        const prefilled = solution.map((row) => row.slice());
        const cells = [];
        for (let r = 0; r < N; r++) {
            for (let c = 0; c < N; c++) cells.push([r, c]);
        }
        PC.rng.shuffle(cells, rng);

        const matchesSolution = (g) => {
            for (let r = 0; r < N; r++) {
                for (let c = 0; c < N; c++) {
                    if (g[r][c] !== solution[r][c]) return false;
                }
            }
            return true;
        };

        let clues = N * N;
        for (const [r, c] of cells) {
            if (keepMin > 0 && clues <= keepMin) break;
            const saved = prefilled[r][c];
            if (saved === 0) continue;
            prefilled[r][c] = 0;
            const res = solveWithTechniques(prefilled, N, boxRows, boxCols, techniques);
            // Accept the removal only if the technique-bounded solve
            // reaches the *correct* full solution. Requiring the exact
            // match (not just "full") is a soundness guard: were any
            // technique buggy enough to make an unsound elimination, it
            // could fill the grid wrongly — this keeps that clue in
            // rather than shipping a puzzle with a broken unique-solution
            // guarantee.
            if (res.solved && matchesSolution(res.grid)) {
                clues -= 1;
            } else {
                prefilled[r][c] = saved; // restore — removal broke solvability
            }
        }
        return { prefilled, clues };
    }

    // -----------------------------------------------------------------
    // Public entry point.
    // -----------------------------------------------------------------

    function generate(size, difficulty, seed) {
        const N = size;
        const { rows: boxRows, cols: boxCols } = boxDims(N);
        const rng = PC.rng.make(seed >>> 0);

        let solution = null;
        for (let i = 0; i < 8 && !solution; i++) {
            solution = placeValidGrid(N, boxRows, boxCols, rng);
        }
        if (!solution) solution = fallbackGrid(N, boxRows, boxCols);

        const techniques = TECHNIQUES_BY_DIFFICULTY[difficulty]
            || TECHNIQUES_BY_DIFFICULTY.medium;
        const keepMin = minClues(N, difficulty);
        const { prefilled, clues } = digHoles(
            solution, N, boxRows, boxCols, techniques, keepMin, rng);

        // Record the technique mix of the canonical solve for insight
        // into how the puzzle actually plays out (surfaced in stats).
        const replay = solveWithTechniques(prefilled, N, boxRows, boxCols, techniques);

        return {
            id: `sudoku-${N}x${N}-${difficulty}-${(seed >>> 0).toString(36)}`,
            game: 'sudoku',
            size: N,
            difficulty,
            boxRows,
            boxCols,
            prefilled,
            solution,
            stats: {
                clues,
                emptyCells: N * N - clues,
                techniqueCounts: replay.techniqueCounts,
            },
        };
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    if (!global.PuzzleGenerators) global.PuzzleGenerators = {};
    global.PuzzleGenerators.sudoku = generate;

    if (!global.PuzzleSolvers) global.PuzzleSolvers = {};
    global.PuzzleSolvers.sudoku = {
        TECHNIQUES_BY_DIFFICULTY,
        placeValidGrid,
        makeState,
        place,
        eliminate,
        candMask,
        nextStep,
        applyStep,
        solveWithTechniques,
        findContradiction,
    };
})(window);
