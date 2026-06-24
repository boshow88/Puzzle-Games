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
        let revealed = false;

        const timer = createTimer(dom.timer);

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
                if (!dom.violations || !dom.violationsText) return;
                if (n > 0) {
                    dom.violations.hidden = false;
                    dom.violations.classList.add('active');
                    dom.violationsText.textContent =
                        `⚠ ${n} conflict${n === 1 ? '' : 's'}`;
                } else {
                    dom.violations.hidden = true;
                    dom.violations.classList.remove('active');
                }
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
                btn.classList.toggle('active', btn.dataset.value === difficulty);
            });
        }

        function syncSizeButtons() {
            if (sizeCfg.kind === 'segmented' && dom.sizeSeg) {
                dom.sizeSeg.querySelectorAll('button').forEach((btn) => {
                    btn.classList.toggle('active',
                        parseInt(btn.dataset.value, 10) === size);
                });
            } else if (sizeCfg.kind === 'slider' && dom.sizeSlider) {
                dom.sizeSlider.value = String(size);
                if (dom.sizeReadout) {
                    dom.sizeReadout.textContent = `${size}×${size}`;
                }
            }
        }

        function startFreshGame() {
            revealed = false;
            syncRevealButton();
            shell.setWin(false);
            onNewGame();
            timer.start();
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
        // Shared hint locale. English is the active default; a future
        // commit will add a UI toggle that flips this to 'zh' and
        // re-renders. Per-game files read this for their hint strings.
        i18n: { locale: 'en' },
    };
})(window);
