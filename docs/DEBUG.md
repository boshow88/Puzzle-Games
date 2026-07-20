# Debug & dev affordances

A running list of the non-shipping hooks baked into the games, so they're easy
to find and strip before a "clean" release. Every in-code hook is also tagged
with a `[DEBUG-HOOK]` comment, so this works too:

```
rg "\[DEBUG-HOOK\]"
```

## URL flags

| Flag | Game | What it does | Where |
| --- | --- | --- | --- |
| `?sudoku_demo=<technique>` | Sudoku | New Game hunts for a hard puzzle that actually uses `<technique>` (e.g. `nakedTriple`, `xWing`, `xyWing`), fast-forwards every step up to it, and pops that hint — so you can eyeball an advanced hint without solving by hand. | `js/games/sudoku.js` |
| `?queens_debug=1` | Queens | Per-attempt generator logging to the console (DFS steps, retries, timing, why a seed bailed). | `js/generators/queens.js` |

## Dev tools (`tools/`)

Standalone pages, not linked from anywhere in the app (no nav points at them),
loaded manually by opening the file. Safe to ship, but they are dev surface:

| Tool | Purpose |
| --- | --- |
| `tools/queens-solver-trace.html` | Step through the Queens generator/solver and inspect each deduction + score. |
| `tools/sudoku-solver-trace.html` | Step through the Sudoku solver technique-by-technique on a generated/seeded puzzle. |
| `tools/tango-solver-trace.html` | Step through the Tango solver's deductions one at a time. |
| `tools/tango-gen-stats.html` | Batch-generate Tango puzzles and inspect generator statistics. |

## Ungated console logging

Not behind any flag — plain defensive/dev `console.warn` / `console.log` that
fires in normal runs. Nothing here changes behaviour, but strip/quiet it if you
want a silent console. Find them with `rg "console\.(log|warn)"`. Current spots:

- `js/generators/tango.js` — row-rejection budget exhausted; "returning unverified".
- `js/games/queens.js` — a solver-state warning.
- `js/games/sudoku.js` — `?sudoku_demo` "technique not reached" warning (only under that flag).
- `js/common.js` — storage read/write + i18n subscriber failures.

## Cleanup checklist

When preparing a release build:

1. `rg "\[DEBUG-HOOK\]"` and remove/guard each URL flag.
2. `rg "console\.(log|warn)"` and quiet anything you don't want shipping.
3. Decide whether to ship or drop the four `tools/` pages.
4. Update this file.
