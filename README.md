# Puzzle Games

A web reimplementation of the LinkedIn-style puzzle games (Queens, Tango, Sudoku, Zip).
Pure static HTML/CSS/JS — deployable on GitHub Pages.

## Status

| Game   | Status        | Notes                                          |
| ------ | ------------- | ---------------------------------------------- |
| Queens | Playable      | Dummy in-browser puzzle generator              |
| Tango  | Playable      | Dummy in-browser puzzle generator              |
| Sudoku | Playable      | 6×6 + 9×9, pencil notes, keypad + keyboard     |
| Zip    | Coming soon   |                                                |

## Layout

```
index.html              Launcher (game picker)
games/*.html            One page per game
css/                    common.css (theme tokens + launcher), game.css (shared game UI)
js/                     common.js + js/games/*.js per-game logic & rendering
data/                   reserved for puzzle JSON pools (not used yet)
```

## Run locally

```powershell
# from repo root
python -m http.server 8000
# then open http://localhost:8000
```

## Deploy on GitHub Pages

Repo Settings → Pages → Source: `main` branch, `/` (root).
All asset paths are relative, so it just works.

## Credits

Game concepts: LinkedIn puzzle games.
Original desktop (tkinter) reference implementation lives in a separate backup repo;
this project keeps the game rules and visual feel, but the level-generation
algorithms are intentionally being redesigned from scratch.
