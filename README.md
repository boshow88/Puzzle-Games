# Puzzle Games

A web reimplementation of the LinkedIn puzzle games (Patches, Queens, Tango, Sudoku, Zip).
Pure static HTML/CSS/JS — deployable on GitHub Pages.

**Play it live:** <https://boshow88.github.io/Puzzle-Games/>

## Status

| Game   | Status        | Notes                                          |
| ------ | ------------- | ---------------------------------------------- |
| Patches| Playable      | Drag-to-draw rectangles, leveled solver + tiered hints, undo & share, 5×5 – 12×12 |
| Queens | Playable      | Region-carving generator (unique, tiered), tactic-bounded hints, undo & share, 5×5 – 12×12 |
| Tango  | Playable      | Dummy in-browser puzzle generator              |
| Sudoku | Playable      | 6×6 / 9×9 / 12×12, notes, undo, shareable links |
| Zip    | Playable      | Drag-to-draw path, unique-solution generator (checkpoints + walls), hint, undo & share, 5×5 – 12×12 |

Full rule reference: [`docs/rules.md`](docs/rules.md).

## Layout

```
index.html              Launcher (game picker)
games/*.html            One page per game
css/                    common.css (theme tokens + launcher), game.css (shared game UI)
js/                     common.js + js/games/*.js (per-game logic/rendering) + js/generators/*.js (puzzle generators & solvers)
data/                   reserved for puzzle JSON pools (not used yet)
docs/rules.md           full rule reference for all five games
```

## Run locally

```powershell
# from repo root
python -m http.server 8000
# then open http://localhost:8000
```

## Deploy on GitHub Pages

Configured via Repo Settings → Pages → Source: `main` branch, `/` (root).
All asset paths are relative, so pushes to `main` redeploy automatically
within a minute or so. No build step.
