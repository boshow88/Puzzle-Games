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
    // Public surface
    // -----------------------------------------------------------------

    global.PuzzleCommon = {
        storage: { readJSON, writeJSON, storageKey },
        prefs: { get: getPrefs, set: setPrefs },
        solves: { log: logSolve, get: getSolveStats },
        timer: createTimer,
        rng: { make: makeRng, pickInt: pickRandomInt, shuffle: shuffleInPlace },
        clamp,
        el,
        svgEl,
    };
})(window);
