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

These are standalone pages, not linked from the app — safe to leave, but they're
part of the dev surface:

| Tool | Purpose |
| --- | --- |
| `tools/queens-solver-trace.html` | Step through the Queens generator/solver and inspect each deduction + score. |
| `tools/sudoku-solver-trace.html` | Step through the Sudoku solver technique-by-technique on a generated/seeded puzzle. |

## Cleanup checklist

When preparing a release build:

1. `rg "\[DEBUG-HOOK\]"` and remove/guard each hook.
2. Decide whether to ship or drop the `tools/` trace pages.
3. Update this file.
