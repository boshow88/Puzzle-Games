/**
 * Puzzle Games — shared utilities
 *
 * Everything in here is intentionally framework-free so it works on
 * GitHub Pages / file:// / `python -m http.server` without any build.
 */
(function (global) {
    'use strict';

    // -----------------------------------------------------------------
    // localStorage helpers
    // -----------------------------------------------------------------

    const STORAGE_PREFIX = 'puzzleGames';

    function storageKey(...parts) {
        return [STORAGE_PREFIX, ...parts].join(':');
    }

    function readJSON(key, fallback) {
        try {
            const raw = localStorage.getItem(key);
            if (raw == null) return fallback;
            return JSON.parse(raw);
        } catch (e) {
            console.warn('[common] readJSON failed for', key, e);
            return fallback;
        }
    }

    function writeJSON(key, value) {
        try {
            localStorage.setItem(key, JSON.stringify(value));
        } catch (e) {
            console.warn('[common] writeJSON failed for', key, e);
        }
    }

    // -----------------------------------------------------------------
    // Per-game preferences (size, difficulty)
    // -----------------------------------------------------------------

    function getPrefs(game) {
        return readJSON(storageKey('prefs', game), {});
    }

    function setPrefs(game, patch) {
        const current = getPrefs(game);
        const next = Object.assign({}, current, patch);
        writeJSON(storageKey('prefs', game), next);
        return next;
    }

    // -----------------------------------------------------------------
    // Solved-puzzle log
    //
    // We store the *count* of solves per (game,size,difficulty) plus a
    // small ring buffer of recent solve timestamps. That's enough for a
    // launcher badge later without saturating localStorage.
    // -----------------------------------------------------------------

    function logSolve(game, size, difficulty, elapsedMs) {
        const key = storageKey('solves', game);
        const data = readJSON(key, { byBucket: {}, recent: [] });
        const bucket = `${size}x${size}:${difficulty}`;
        data.byBucket[bucket] = (data.byBucket[bucket] || 0) + 1;
        data.recent.unshift({
            t: Date.now(),
            size,
            difficulty,
            elapsedMs: elapsedMs || null,
        });
        data.recent = data.recent.slice(0, 25);
        writeJSON(key, data);
    }

    function getSolveStats(game) {
        return readJSON(storageKey('solves', game), { byBucket: {}, recent: [] });
    }

    // -----------------------------------------------------------------
    // Timer
    // -----------------------------------------------------------------

    function createTimer(displayEl) {
        let startedAt = null;
        let rafId = null;
        let stopped = true;

        function format(ms) {
            const s = Math.floor(ms / 1000);
            const mm = String(Math.floor(s / 60)).padStart(2, '0');
            const ss = String(s % 60).padStart(2, '0');
            return `${mm}:${ss}`;
        }

        function tick() {
            if (stopped) return;
            const ms = Date.now() - startedAt;
            if (displayEl) displayEl.textContent = format(ms);
            rafId = requestAnimationFrame(tick);
        }

        return {
            start() {
                stopped = false;
                startedAt = Date.now();
                if (displayEl) displayEl.textContent = format(0);
                cancelAnimationFrame(rafId);
                rafId = requestAnimationFrame(tick);
            },
            stop() {
                stopped = true;
                cancelAnimationFrame(rafId);
                return startedAt != null ? Date.now() - startedAt : 0;
            },
            reset() {
                this.stop();
                startedAt = null;
                if (displayEl) displayEl.textContent = format(0);
            },
            elapsed() {
                if (startedAt == null) return 0;
                return (stopped ? 0 : Date.now() - startedAt);
            },
        };
    }

    // -----------------------------------------------------------------
    // Tiny PRNG so puzzle generation is reproducible from a seed.
    // mulberry32 — small, fast, good-enough for level shuffling.
    // -----------------------------------------------------------------

    function makeRng(seed) {
        let a = (seed >>> 0) || 1;
        return function () {
            a |= 0;
            a = (a + 0x6d2b79f5) | 0;
            let t = a;
            t = Math.imul(t ^ (t >>> 15), t | 1);
            t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
            return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
        };
    }

    function pickRandomInt(rng, min, maxExclusive) {
        return Math.floor(rng() * (maxExclusive - min)) + min;
    }

    function shuffleInPlace(arr, rng) {
        for (let i = arr.length - 1; i > 0; i--) {
            const j = Math.floor(rng() * (i + 1));
            const tmp = arr[i];
            arr[i] = arr[j];
            arr[j] = tmp;
        }
        return arr;
    }

    // -----------------------------------------------------------------
    // Misc
    // -----------------------------------------------------------------

    function clamp(value, min, max) {
        return Math.min(max, Math.max(min, value));
    }

    function el(tag, attrs, ...children) {
        const node = document.createElement(tag);
        if (attrs) {
            for (const k in attrs) {
                if (k === 'class') node.className = attrs[k];
                else if (k === 'text') node.textContent = attrs[k];
                else if (k.startsWith('on') && typeof attrs[k] === 'function') {
                    node.addEventListener(k.slice(2).toLowerCase(), attrs[k]);
                } else if (attrs[k] != null) {
                    node.setAttribute(k, attrs[k]);
                }
            }
        }
        for (const c of children) {
            if (c == null) continue;
            node.appendChild(typeof c === 'string' ? document.createTextNode(c) : c);
        }
        return node;
    }

    function svgEl(tag, attrs) {
        const node = document.createElementNS('http://www.w3.org/2000/svg', tag);
        if (attrs) {
            for (const k in attrs) {
                if (attrs[k] != null) node.setAttribute(k, attrs[k]);
            }
        }
        return node;
    }

    // -----------------------------------------------------------------
    // Game shell
    //
    // Every game page shares the same chrome: a difficulty segmented
    // control, a size selector (slider or segmented), New / Reset /
    // Reveal buttons, a timer, and a win badge. `createShell` owns that
    // wiring so each game only writes its own rules + rendering.
    //
    // The shell handles:
    //   - Reading / writing prefs (game id namespaced).
    //   - Wiring difficulty buttons; difficulty values are read from
    //     `data-value` on the segmented control's buttons.
    //   - Wiring the size control. Two kinds:
    //       { kind: 'slider', min, max, default }
    //       { kind: 'segmented', default }   (values from data-value)
    //     The shell expects the matching DOM ids in the page.
    //   - Wiring New / Reset / Reveal buttons.
    //   - Owning `shell.revealed` and keeping the button's
    //     `active` class + `aria-pressed` in sync. Whenever a new game
    //     starts the shell resets `revealed` to false automatically.
    //   - Creating a Timer bound to `#timer`.
    //   - `setWin(bool)` toggling `#win-message` visibility.
    //   - `setViolationCount(n)` for the three games that share the
    //     "⚠ N conflict(s)" pill format. Zip ignores this and writes
    //     into its own pill element directly.
    //
    // The game supplies callbacks:
    //   onNewGame()         — start a fresh puzzle (timer is auto-started
    //                         by the shell *after* onNewGame returns)
    //   onReset()           — clear placements but keep the same puzzle
    //                         (also followed by an auto timer restart)
    //   onReveal(revealed)  — repaint to reflect the new reveal state
    //
    // Returned shell object exposes:
    //   shell.dom.board    — the SVG board element
    //   shell.timer        — PC.timer instance (already wired to #timer)
    //   shell.difficulty   — current difficulty string
    //   shell.size         — current size number
    //   shell.revealed     — current reveal flag (read-only from games)
    //   shell.setWin(b)
    //   shell.setViolationCount(n)
    //   shell.markSolved() — convenience: stops timer + logs solve +
    //                        sets win. Returns elapsed ms.
    //   shell.start()      — fire the first game. Caller is responsible
    //                        for invoking this after attaching their
    //                        own board listeners.
    // -----------------------------------------------------------------

    const DIFFICULTY_VALUES = ['easy', 'medium', 'hard'];

    function createShell(opts) {
        const gameId = opts.gameId;
        const sizeCfg = opts.size;
        const diffCfg = opts.difficulty || { default: 'medium' };
        const onNewGame = opts.onNewGame || (() => {});
        const onReset = opts.onReset || (() => {});
        const onReveal = opts.onReveal || (() => {});

        const dom = {
            board: document.getElementById('board'),
            difficultySeg: document.getElementById('difficulty-seg'),
            sizeSeg: document.getElementById('size-seg'),
            sizeSlider: document.getElementById('size-slider'),
            sizeReadout: document.getElementById('size-readout'),
            newGameBtn: document.getElementById('new-game-btn'),
            resetBtn: document.getElementById('reset-btn'),
            revealBtn: document.getElementById('reveal-btn'),
            timer: document.getElementById('timer'),
            violations: document.getElementById('violations'),
            violationsText: document.getElementById('violations-text'),
            winMessage: document.getElementById('win-message'),
        };

        // Size / difficulty intentionally do NOT persist across reloads —
        // we always boot at each game's declared default. Stats (solve
        // counts) are still tracked via the separate `solves:<game>` key.
        let segmentedSizes = null;
        if (sizeCfg.kind === 'segmented' && dom.sizeSeg) {
            segmentedSizes = Array.from(dom.sizeSeg.querySelectorAll('button'))
                .map((b) => parseInt(b.dataset.value, 10))
                .filter((n) => !Number.isNaN(n));
        }

        let difficulty = diffCfg.default;
        let size = sizeCfg.kind === 'slider'
            ? clamp(sizeCfg.default, sizeCfg.min, sizeCfg.max)
            : sizeCfg.default;
        // "Committed" mirrors the difficulty/size that the currently
        // displayed puzzle was generated with. It diverges from
        // `difficulty`/`size` the moment the player picks a new value
        // in the toolbar and snaps back when they press New Game.
        // The toolbar paints both states so the player can see what's
        // running and what they've staged.
        let appliedDifficulty = difficulty;
        let appliedSize = size;
        let revealed = false;

        const timer = createTimer(dom.timer);

        // Last-rendered conflict count, kept so a locale change can
        // re-render the violations pill without the game needing to
        // know to recall setViolationCount.
        let lastViolationN = 0;

        function renderViolationCount() {
            if (!dom.violations || !dom.violationsText) return;
            if (lastViolationN > 0) {
                dom.violations.hidden = false;
                dom.violations.classList.add('active');
                dom.violationsText.textContent =
                    global.PuzzleCommon.i18n.t('conflict', lastViolationN);
            } else {
                dom.violations.hidden = true;
                dom.violations.classList.remove('active');
            }
        }

        // Subscribe BEFORE returning the shell so games that never
        // call setViolationCount (Zip) still get any future label
        // re-renders for free.
        global.PuzzleCommon.i18n.subscribe(renderViolationCount);

        const shell = {
            dom,
            timer,
            get difficulty() { return difficulty; },
            get size() { return size; },
            get revealed() { return revealed; },
            setWin(b) {
                if (dom.winMessage) dom.winMessage.hidden = !b;
            },
            setViolationCount(n) {
                lastViolationN = n;
                renderViolationCount();
            },
            markSolved() {
                const elapsed = timer.stop();
                logSolve(gameId, size, difficulty, elapsed);
                shell.setWin(true);
                return elapsed;
            },
        };

        function syncRevealButton() {
            if (!dom.revealBtn) return;
            dom.revealBtn.classList.toggle('active', revealed);
            dom.revealBtn.setAttribute(
                'aria-pressed', revealed ? 'true' : 'false');
        }

        function syncDifficultyButtons() {
            if (!dom.difficultySeg) return;
            dom.difficultySeg.querySelectorAll('button').forEach((btn) => {
                const v = btn.dataset.value;
                btn.classList.toggle('active', v === difficulty);
                btn.classList.toggle('committed', v === appliedDifficulty);
            });
        }

        function syncSizeButtons() {
            if (sizeCfg.kind === 'segmented' && dom.sizeSeg) {
                dom.sizeSeg.querySelectorAll('button').forEach((btn) => {
                    const v = parseInt(btn.dataset.value, 10);
                    btn.classList.toggle('active', v === size);
                    btn.classList.toggle('committed', v === appliedSize);
                });
            } else if (sizeCfg.kind === 'slider' && dom.sizeSlider) {
                dom.sizeSlider.value = String(size);
                if (dom.sizeReadout) {
                    if (size === appliedSize) {
                        dom.sizeReadout.textContent = `${size}×${size}`;
                        dom.sizeReadout.classList.remove('pending');
                    } else {
                        // Render "current → pending" so the player can
                        // tell at a glance that the slider value isn't
                        // yet what the board shows.
                        dom.sizeReadout.innerHTML = '';
                        const cur = document.createElement('span');
                        cur.className = 'readout-current';
                        cur.textContent = `${appliedSize}×${appliedSize}`;
                        const arrow = document.createElement('span');
                        arrow.className = 'readout-arrow';
                        arrow.textContent = '→';
                        const next = document.createElement('span');
                        next.className = 'readout-next';
                        next.textContent = `${size}×${size}`;
                        dom.sizeReadout.appendChild(cur);
                        dom.sizeReadout.appendChild(arrow);
                        dom.sizeReadout.appendChild(next);
                        dom.sizeReadout.classList.add('pending');
                    }
                }
            }
        }

        let isGenerating = false;
        async function startFreshGame() {
            if (isGenerating) return;
            isGenerating = true;
            try {
                // Commit the toolbar's pending selection — the board is
                // about to regenerate at these values.
                appliedDifficulty = difficulty;
                appliedSize = size;
                syncDifficultyButtons();
                syncSizeButtons();
                revealed = false;
                syncRevealButton();
                shell.setWin(false);
                if (dom.newGameBtn) dom.newGameBtn.disabled = true;
                progress.start(t('generatingPuzzle'));
                // Let the browser paint the overlay (still invisible
                // thanks to its CSS fade-in delay) before we hand the
                // main thread to the generator. The fade-in then
                // continues on the compositor thread even while
                // onNewGame() blocks.
                await progress.waitNextPaint();
                try {
                    await onNewGame();
                } finally {
                    progress.finish();
                    if (dom.newGameBtn) dom.newGameBtn.disabled = false;
                }
                timer.start();
            } finally {
                isGenerating = false;
            }
        }

        function applyReset() {
            shell.setWin(false);
            onReset();
            timer.start();
        }

        // Difficulty / size selection updates only the toolbar state.
        // The actual puzzle isn't regenerated until the player clicks
        // New Game — this lets them flip multiple settings at once
        // without spawning a throwaway puzzle in between.
        function setDifficulty(value) {
            if (!DIFFICULTY_VALUES.includes(value)) return;
            if (value === difficulty) return;
            difficulty = value;
            syncDifficultyButtons();
        }

        function setSize(rawValue) {
            let n;
            if (sizeCfg.kind === 'slider') {
                n = clamp(parseInt(rawValue, 10) || sizeCfg.default,
                    sizeCfg.min, sizeCfg.max);
            } else {
                n = parseInt(rawValue, 10);
                if (!segmentedSizes || !segmentedSizes.includes(n)) return;
            }
            if (n === size) return;
            size = n;
            syncSizeButtons();
        }

        function toggleReveal() {
            revealed = !revealed;
            syncRevealButton();
            onReveal(revealed);
        }

        // ---------- wire DOM events ----------

        if (dom.difficultySeg) {
            dom.difficultySeg.querySelectorAll('button').forEach((btn) => {
                btn.addEventListener('click',
                    () => setDifficulty(btn.dataset.value));
            });
        }

        if (sizeCfg.kind === 'segmented' && dom.sizeSeg) {
            dom.sizeSeg.querySelectorAll('button').forEach((btn) => {
                btn.addEventListener('click',
                    () => setSize(btn.dataset.value));
            });
        } else if (sizeCfg.kind === 'slider' && dom.sizeSlider) {
            dom.sizeSlider.addEventListener('change',
                (ev) => setSize(ev.target.value));
        }

        if (dom.newGameBtn) {
            dom.newGameBtn.addEventListener('click', startFreshGame);
        }
        if (dom.resetBtn) {
            dom.resetBtn.addEventListener('click', applyReset);
        }
        if (dom.revealBtn) {
            dom.revealBtn.addEventListener('click', toggleReveal);
        }

        // ---------- initial paint ----------

        syncDifficultyButtons();
        syncSizeButtons();
        syncRevealButton();
        shell.setWin(false);

        // The caller decides when to fire the first game (after attaching
        // its own board listeners) by calling shell.start().
        shell.start = startFreshGame;

        return shell;
    }

    // -----------------------------------------------------------------
    // Public surface
    // -----------------------------------------------------------------

    // -----------------------------------------------------------------
    // i18n
    //
    // English is the active default. Users can flip to 'zh' via the
    // lang-toggle in every page's topbar; the choice is persisted to
    // localStorage so reloads keep it.
    //
    // Strings table is intentionally flat: one key → one string (or
    // formatter function) per locale. Games can extend it at load
    // time by mutating PC.i18n.STRINGS[loc] before subscribers fire.
    //
    // Translation reaches the DOM through `data-i18n="key"` attrs on
    // any element that should carry localised text:
    //   <span data-i18n="difficulty">Difficulty</span>
    // Plus `data-i18n-title="..."` for tooltips and
    // `data-i18n-aria-label="..."` for ARIA labels.
    //
    // Anything dynamic (the violations pill, the hint banner) calls
    // PC.i18n.subscribe(cb) so it knows to re-render on a locale
    // change without an extra event-bus.
    // -----------------------------------------------------------------

    const STRINGS = {
        en: {
            // Shared topbar / toolbar / actions
            menu: '← Menu',
            language: 'Language',
            generatingPuzzle: 'Generating puzzle…',
            difficulty: 'Difficulty',
            easy: 'Easy',
            medium: 'Medium',
            hard: 'Hard',
            boardSize: 'Board size',
            gameSettings: 'Game settings',
            newGame: 'New Game',
            reset: '↻ Reset',
            hint: '💡 Hint',
            reveal: '? Reveal',
            share: '🔗 Share',
            shareTitle: 'Copy a link to this puzzle',
            shareCopied: 'Link copied!',
            shareFailed: 'Copy failed — copy from the address bar instead.',
            winMessage: 'You Win! ✨',
            howToPlay: 'How to play',
            conflict: (n) => `⚠ ${n} conflict${n === 1 ? '' : 's'}`,
            clearPlacements: 'Clear placements',
            clearPath: 'Clear path',
            highlightDeducible: 'Highlight one deducible cell',
            showSolution: 'Show solution overlay',
            showSolutionPath: 'Show solution path',

            // Index / launcher
            appTitle: 'Puzzle Games',
            appSubtitle: "A collection of logic puzzles inspired by LinkedIn's daily games.",
            playable: 'Playable',
            wip: 'WIP',
            builtNote: 'Built as a static site — works offline, deployable on GitHub Pages.',

            // Queens
            queensName: 'Queens',
            queensTagline: 'Royal regions, one queen each.',
            queensCardBody:
                'Place N queens so that every row, column, color region and 8-neighborhood contains exactly one.',
            queensBoardAria: 'Queens puzzle board',
            queensHelp1Html:
                'Click a cell to cycle through <strong>empty → × → ♛</strong> (× is just a personal "no" marker).',
            queensHelp2:
                'Every row, every column, every color region, and every 3×3 neighborhood may contain at most one queen.',
            queensHelp3:
                'Solve the board by placing exactly N queens — one per row, column, and region — with no two adjacent.',

            // Tango
            tangoName: 'Tango',
            tangoTagline: 'Sun & moon balance.',
            tangoCardBody:
                'Fill the grid with suns and moons — half of each per row and column, no three in a row, respect the walls.',
            tangoBoardAria: 'Tango puzzle board',
            tangoHelp1Html:
                'Click a cell to cycle through <strong>empty → ☀ → ☾</strong>. Pre-filled cells are locked.',
            tangoHelp2Html:
                'Each row and column must contain <strong>half suns and half moons</strong>, and never three of the same in a row.',
            tangoHelp3Html:
                'The badges between cells are constraints: <strong>=</strong> means the two neighbours must match, <strong>×</strong> means they must differ.',
            tangoHelp4: 'The puzzle is solved when every cell is filled and no rule is broken.',

            // Sudoku
            sudokuName: 'Sudoku',
            sudokuTagline: 'Classic number logic.',
            sudokuCardBody:
                'Fill the grid so every row, column and box contains each digit exactly once.',
            sudokuBoardAria: 'Sudoku puzzle board',
            sudokuNumPadAria: 'Number pad',
            sudokuNotes: '✎ Notes',
            sudokuErase: '⌫ Erase',
            sudokuEraseAria: 'Erase',
            sudokuEraseTitle: 'Erase (Backspace / Delete / 0)',
            sudokuHelp1: 'Click a cell to select it. Pre-filled (locked) cells stay grey.',
            sudokuHelp2:
                'Fill a digit with the on-screen keypad or your keyboard. The same key again clears that digit.',
            sudokuHelp3Html:
                'Toggle <strong>✎ Notes</strong> (or press <kbd>N</kbd>) to write small candidate marks instead of a full digit.',
            sudokuHelp4Html:
                'Each <strong>row</strong>, <strong>column</strong> and <strong>box</strong> must contain every digit exactly once.',
            sudokuHelp5Html:
                '<kbd>Backspace</kbd> / <kbd>Delete</kbd> / <kbd>0</kbd> clears the cell. Arrow keys move the selection.',

            // Zip
            zipName: 'Zip',
            zipTagline: 'One path, every cell.',
            zipCardBodyHtml:
                'Drag from <strong>1</strong> to draw a single path covering every open cell, hitting checkpoints in numerical order.',
            zipBoardAria: 'Zip puzzle board',
            zipHelp1Html:
                'Drag from the cell marked <strong>1</strong> to draw a path through every white cell.',
            zipHelp2Html:
                'Visit the numbered checkpoints in order — <strong>1 → 2 → 3 → … → N</strong>.',
            zipHelp3Html:
                'The path cannot cross black <strong>walls</strong> or enter grey <strong>holes</strong>; only orthogonal moves.',
            zipHelp4:
                'You can pick up the drag from any cell already on the path — everything after that cell is dropped.',
            zipHelp5:
                'Solved when the path covers every white cell with checkpoints in the right order.',
        },
        zh: {
            menu: '← 選單',
            language: '語言',
            generatingPuzzle: '正在產生關卡…',
            difficulty: '難度',
            easy: '簡單',
            medium: '中等',
            hard: '困難',
            boardSize: '盤面大小',
            gameSettings: '遊戲設定',
            newGame: '新局',
            reset: '↻ 重設',
            hint: '💡 提示',
            reveal: '? 解答',
            share: '🔗 分享',
            shareTitle: '複製本關卡的連結',
            shareCopied: '連結已複製！',
            shareFailed: '複製失敗 — 請從網址列手動複製。',
            winMessage: '你贏了！ ✨',
            howToPlay: '遊玩方式',
            conflict: (n) => `⚠ ${n} 個衝突`,
            clearPlacements: '清除目前的標記',
            clearPath: '清除路徑',
            highlightDeducible: '標出一格可推論的位置',
            showSolution: '顯示解答',
            showSolutionPath: '顯示解答路徑',

            appTitle: 'Puzzle Games',
            appSubtitle: '一組受 LinkedIn 每日小遊戲啟發的邏輯謎題。',
            playable: '可玩',
            wip: '開發中',
            builtNote: '純靜態網站 — 可離線使用，也可部署於 GitHub Pages。',

            queensName: 'Queens',
            queensTagline: '皇家領地，每區一后。',
            queensCardBody: '在每個列、行、色塊區域與 8 鄰域中各放一個皇后。',
            queensBoardAria: 'Queens 盤面',
            queensHelp1Html:
                '點擊格子在 <strong>空 → × → ♛</strong> 之間循環（× 為個人「不放這」的標記）。',
            queensHelp2:
                '每個列、每個行、每個色塊區域、每個 3×3 鄰域中，最多只能有一個皇后。',
            queensHelp3:
                '在不違反規則的情況下放下 N 個皇后即過關 — 每列、每行、每區域各一，且不互相相鄰。',

            tangoName: 'Tango',
            tangoTagline: '太陽與月亮的平衡。',
            tangoCardBody:
                '用太陽和月亮填滿盤面 — 每列每行各半，不能連續三個相同，並遵循牆的限制。',
            tangoBoardAria: 'Tango 盤面',
            tangoHelp1Html:
                '點擊格子在 <strong>空 → ☀ → ☾</strong> 之間循環。預填的格子是鎖定的。',
            tangoHelp2Html:
                '每列、每行必須是<strong>半數太陽、半數月亮</strong>，且不能連續三個相同。',
            tangoHelp3Html:
                '格子間的標記是限制：<strong>=</strong> 表示兩格相同，<strong>×</strong> 表示兩格相異。',
            tangoHelp4: '所有格子都填滿、且無違規時即過關。',

            sudokuName: 'Sudoku',
            sudokuTagline: '經典數字邏輯。',
            sudokuCardBody:
                '填滿盤面，使每列、每行、每宮都恰好包含 1 至 N 各一次。',
            sudokuBoardAria: 'Sudoku 盤面',
            sudokuNumPadAria: '數字鍵盤',
            sudokuNotes: '✎ 便箋',
            sudokuErase: '⌫ 清除',
            sudokuEraseAria: '清除',
            sudokuEraseTitle: '清除（Backspace / Delete / 0）',
            sudokuHelp1: '點擊格子選取它。預填（鎖定）的格子為灰色。',
            sudokuHelp2:
                '用螢幕鍵盤或實體鍵盤輸入數字。再按一次同一個鍵會清除該數字。',
            sudokuHelp3Html:
                '切換 <strong>✎ 便箋</strong>（或按 <kbd>N</kbd>）可寫入小型候選數字，而非正式數字。',
            sudokuHelp4Html:
                '每個 <strong>列</strong>、<strong>行</strong>、<strong>宮</strong> 都必須恰好包含每個數字各一次。',
            sudokuHelp5Html:
                '<kbd>Backspace</kbd> / <kbd>Delete</kbd> / <kbd>0</kbd> 清除格子；方向鍵移動選取。',

            zipName: 'Zip',
            zipTagline: '一條路徑，貫穿每格。',
            zipCardBodyHtml:
                '從 <strong>1</strong> 開始拖曳，畫出一條覆蓋每個白色格子的路徑，並依序通過編號的檢查點。',
            zipBoardAria: 'Zip 盤面',
            zipHelp1Html:
                '從標示 <strong>1</strong> 的格子開始拖曳，畫一條經過每個白色格子的路徑。',
            zipHelp2Html:
                '依數字順序通過檢查點 — <strong>1 → 2 → 3 → … → N</strong>。',
            zipHelp3Html:
                '路徑不能越過黑色 <strong>牆</strong>，也不能進入灰色 <strong>洞</strong>；只能沿正交方向移動。',
            zipHelp4:
                '可以從路徑上任何一格重新拖曳 — 該格之後的部分都會被取消。',
            zipHelp5: '當路徑覆蓋每個白格，且檢查點都依序通過時即過關。',
        },
    };

    const LANG_KEY = storageKey('lang');
    const LANG_SUPPORTED = ['en', 'zh'];
    const localeSubscribers = new Set();
    let currentLocale = readJSON(LANG_KEY, 'en');
    if (!LANG_SUPPORTED.includes(currentLocale)) currentLocale = 'en';

    function tForLocale(loc, key, ...args) {
        const table = STRINGS[loc] || STRINGS.en;
        let entry = table[key];
        if (entry == null) entry = STRINGS.en[key];
        if (entry == null) return key;
        return typeof entry === 'function' ? entry(...args) : entry;
    }

    function t(key, ...args) {
        return tForLocale(currentLocale, key, ...args);
    }

    function translateNode(rootEl) {
        if (!rootEl) return;
        const isHtmlKey = (key) => /Html$/.test(key);
        const textNodes = rootEl.querySelectorAll('[data-i18n]');
        for (const el of textNodes) {
            const key = el.getAttribute('data-i18n');
            const text = t(key);
            if (isHtmlKey(key)) el.innerHTML = text;
            else el.textContent = text;
        }
        const titleNodes = rootEl.querySelectorAll('[data-i18n-title]');
        for (const el of titleNodes) {
            el.setAttribute('title', t(el.getAttribute('data-i18n-title')));
        }
        const ariaNodes = rootEl.querySelectorAll('[data-i18n-aria-label]');
        for (const el of ariaNodes) {
            el.setAttribute('aria-label', t(el.getAttribute('data-i18n-aria-label')));
        }
    }

    function setLocale(newLoc) {
        if (!LANG_SUPPORTED.includes(newLoc)) return;
        if (newLoc === currentLocale) return;
        currentLocale = newLoc;
        writeJSON(LANG_KEY, currentLocale);
        document.documentElement.lang = currentLocale === 'zh' ? 'zh-Hant' : 'en';
        translateNode(document);
        syncLangToggle();
        for (const cb of localeSubscribers) {
            try { cb(currentLocale); } catch (e) { console.warn('[i18n] subscriber threw', e); }
        }
    }

    function subscribe(cb) {
        localeSubscribers.add(cb);
        return () => localeSubscribers.delete(cb);
    }

    function syncLangToggle() {
        const tog = document.getElementById('lang-toggle');
        if (!tog) return;
        for (const btn of tog.querySelectorAll('button[data-lang]')) {
            const isActive = btn.dataset.lang === currentLocale;
            btn.classList.toggle('active', isActive);
            btn.setAttribute('aria-checked', isActive ? 'true' : 'false');
        }
    }

    function wireLangToggle() {
        const tog = document.getElementById('lang-toggle');
        if (!tog) return;
        tog.addEventListener('click', (ev) => {
            const btn = ev.target.closest('button[data-lang]');
            if (!btn) return;
            setLocale(btn.dataset.lang);
        });
        syncLangToggle();
    }

    function bootstrapI18n() {
        document.documentElement.lang = currentLocale === 'zh' ? 'zh-Hant' : 'en';
        translateNode(document);
        wireLangToggle();
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', bootstrapI18n);
    } else {
        bootstrapI18n();
    }

    // -----------------------------------------------------------------
    // Progress indicator
    //
    // A single shared overlay rendered into `.board-wrap` (or the body,
    // if no board exists) while a long synchronous task — currently
    // just puzzle generation — runs on the main thread. The visible
    // part is delayed by ~250ms via a CSS keyframe so quick generations
    // don't flash a card on screen for ~50ms.
    //
    // The indeterminate progress bar is driven entirely by a CSS
    // transform animation. Compositor-thread animations keep ticking
    // even when the JS thread is blocked, so the bar continues to
    // visibly move during a multi-second generate() call without us
    // needing to make the generator async.
    // -----------------------------------------------------------------

    const progress = (function () {
        let overlay = null;
        let textEl = null;
        let attachedTo = null;
        let activeCount = 0;

        function ensureDom(host) {
            if (overlay && attachedTo === host) return;
            if (overlay && overlay.parentNode) overlay.parentNode.removeChild(overlay);
            overlay = document.createElement('div');
            overlay.className = 'puzzle-progress';
            overlay.setAttribute('role', 'status');
            overlay.setAttribute('aria-live', 'polite');
            overlay.hidden = true;
            const card = document.createElement('div');
            card.className = 'puzzle-progress-card';
            textEl = document.createElement('div');
            textEl.className = 'puzzle-progress-text';
            const bar = document.createElement('div');
            bar.className = 'puzzle-progress-bar';
            const fill = document.createElement('span');
            fill.className = 'puzzle-progress-bar-fill';
            bar.appendChild(fill);
            card.appendChild(textEl);
            card.appendChild(bar);
            overlay.appendChild(card);
            host.appendChild(overlay);
            attachedTo = host;
        }

        function resolveHost() {
            return document.querySelector('.board-wrap')
                || document.querySelector('main')
                || document.body;
        }

        function start(text) {
            const host = resolveHost();
            ensureDom(host);
            // Reset the keyframe so each new generate restarts its
            // fade-in delay. Cheap trick: remove + reflow + add the
            // running class.
            textEl.textContent = text || '';
            overlay.classList.remove('is-running', 'is-determinate');
            const fillEl = overlay.querySelector('.puzzle-progress-bar-fill');
            if (fillEl) {
                fillEl.style.width = '';
                fillEl.style.transform = '';
            }
            overlay.hidden = false;
            void overlay.offsetWidth;
            overlay.classList.add('is-running');
            activeCount += 1;
        }

        function update(text) {
            if (!textEl) return;
            textEl.textContent = text || '';
        }

        // Switch the bar to determinate mode and set its fill ratio
        // (0..1). First call also kills the indeterminate slide
        // animation. Safe to call repeatedly with the same overlay.
        function setFraction(fraction) {
            if (!overlay) return;
            const fillEl = overlay.querySelector('.puzzle-progress-bar-fill');
            if (!fillEl) return;
            if (!overlay.classList.contains('is-determinate')) {
                overlay.classList.add('is-determinate');
            }
            const f = Math.max(0, Math.min(1, fraction));
            fillEl.style.width = (f * 100).toFixed(2) + '%';
        }

        function finish() {
            if (activeCount > 0) activeCount -= 1;
            if (activeCount > 0) return;
            if (overlay) {
                overlay.classList.remove('is-running', 'is-determinate');
                overlay.hidden = true;
            }
        }

        function waitNextPaint() {
            return new Promise((resolve) => {
                requestAnimationFrame(() => {
                    requestAnimationFrame(() => resolve());
                });
            });
        }

        return { start, update, setFraction, finish, waitNextPaint };
    })();

    // -----------------------------------------------------------------
    // Share helpers
    //
    // A game page that wants shareable URLs publishes its current
    // (size, difficulty, seed) into the address bar via
    // `share.replaceUrl(...)` after every successful generation. The
    // friend who opens the link reads the same three values via
    // `share.readParams()` on boot and uses them to seed their first
    // puzzle. Anything missing or malformed is silently ignored —
    // partial state is treated as "no shared puzzle, use defaults".
    //
    // The seed travels as base36 (uint32 → up to 7 chars) to match
    // the format already baked into `puzzle.id`. Determinism of the
    // generator given (size, difficulty, seed) is the contract that
    // makes this work end-to-end.
    // -----------------------------------------------------------------

    const share = (function () {
        const KEY_SIZE = 'size';
        const KEY_DIFF = 'diff';
        const KEY_SEED = 'seed';

        function parseSeed(raw) {
            if (raw == null) return null;
            // base36 uint32 — matches puzzle.id encoding.
            const n = parseInt(String(raw).trim(), 36);
            if (!Number.isFinite(n) || n < 0) return null;
            return (n >>> 0);
        }

        function formatSeed(n) {
            return ((n >>> 0)).toString(36);
        }

        function readParams() {
            try {
                const sp = new URL(location.href).searchParams;
                const sizeRaw = sp.get(KEY_SIZE);
                const sizeNum = sizeRaw == null ? null
                    : parseInt(sizeRaw, 10);
                return {
                    size: Number.isFinite(sizeNum) ? sizeNum : null,
                    difficulty: sp.get(KEY_DIFF),
                    seed: parseSeed(sp.get(KEY_SEED)),
                };
            } catch (e) {
                return { size: null, difficulty: null, seed: null };
            }
        }

        function replaceUrl(params) {
            try {
                const url = new URL(location.href);
                if (params.size != null) {
                    url.searchParams.set(KEY_SIZE, String(params.size));
                }
                if (params.difficulty != null) {
                    url.searchParams.set(KEY_DIFF, params.difficulty);
                }
                if (params.seed != null) {
                    url.searchParams.set(KEY_SEED, formatSeed(params.seed));
                }
                history.replaceState(null, '', url.toString());
            } catch (e) {
                // history API can throw on file:// — silently ignore so
                // the rest of the page keeps working.
            }
        }

        async function copyCurrentUrl() {
            return copyText(location.href);
        }

        async function copyText(text) {
            try {
                if (navigator.clipboard && navigator.clipboard.writeText) {
                    await navigator.clipboard.writeText(text);
                    return true;
                }
            } catch (e) {
                // Permissions denied / not in secure context — fall
                // through to the legacy path.
            }
            try {
                const ta = document.createElement('textarea');
                ta.value = text;
                ta.setAttribute('readonly', '');
                ta.style.position = 'fixed';
                ta.style.top = '0';
                ta.style.left = '0';
                ta.style.opacity = '0';
                document.body.appendChild(ta);
                ta.select();
                const ok = document.execCommand
                    && document.execCommand('copy');
                document.body.removeChild(ta);
                return !!ok;
            } catch (e) {
                return false;
            }
        }

        return { readParams, replaceUrl, copyCurrentUrl, copyText };
    })();

    // -----------------------------------------------------------------
    // Toast
    //
    // A single shared pill-shaped notice that fades in at the bottom
    // of the viewport for a couple of seconds. Used for transient
    // confirmations like "link copied" — anything that demands user
    // attention should still go through a modal/alert.
    // -----------------------------------------------------------------

    const toast = (function () {
        let el = null;
        let hideTimer = null;

        function ensureEl() {
            if (el) return el;
            el = document.createElement('div');
            el.className = 'toast';
            el.setAttribute('role', 'status');
            el.setAttribute('aria-live', 'polite');
            document.body.appendChild(el);
            return el;
        }

        function show(text, ms) {
            const node = ensureEl();
            node.textContent = text || '';
            // Restart the fade so consecutive show() calls reset
            // their own timer rather than inheriting the previous.
            node.classList.remove('toast-visible');
            void node.offsetWidth;
            node.classList.add('toast-visible');
            if (hideTimer) clearTimeout(hideTimer);
            hideTimer = setTimeout(() => {
                node.classList.remove('toast-visible');
            }, ms || 1800);
        }

        return { show };
    })();

    global.PuzzleCommon = {
        storage: { readJSON, writeJSON, storageKey },
        prefs: { get: getPrefs, set: setPrefs },
        solves: { log: logSolve, get: getSolveStats },
        timer: createTimer,
        shell: { create: createShell },
        rng: { make: makeRng, pickInt: pickRandomInt, shuffle: shuffleInPlace },
        clamp,
        el,
        svgEl,
        i18n: {
            get locale() { return currentLocale; },
            setLocale,
            t,
            tForLocale,
            subscribe,
            translateNode,
            STRINGS,
        },
        progress,
        share,
        toast,
    };
})(window);
