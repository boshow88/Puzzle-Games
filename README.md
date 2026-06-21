# Puzzle Games

A web reimplementation of the LinkedIn puzzle games (Queens, Tango, Sudoku, Zip).
Pure static HTML/CSS/JS — deployable on GitHub Pages.

**Play it live:** <https://boshow88.github.io/Puzzle-Games/>

## Status

| Game   | Status        | Notes                                          |
| ------ | ------------- | ---------------------------------------------- |
| Queens | Playable      | Dummy in-browser puzzle generator              |
| Tango  | Playable      | Dummy in-browser puzzle generator              |
| Sudoku | Playable      | 6×6 + 9×9, pencil notes, keypad + keyboard     |
| Zip    | Playable      | Drag-to-draw path, walls + holes, 5×5 – 12×12   |

Full rule reference: [`docs/rules.md`](docs/rules.md).

## Layout

```
index.html              Launcher (game picker)
games/*.html            One page per game
css/                    common.css (theme tokens + launcher), game.css (shared game UI)
js/                     common.js + js/games/*.js per-game logic & rendering
data/                   reserved for puzzle JSON pools (not used yet)
docs/rules.md           full rule reference for all four games
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
