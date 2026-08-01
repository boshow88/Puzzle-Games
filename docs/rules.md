# Game Rules

A central reference for the five puzzles in this collection. Each game
page already shows a short *How to play* footer; this document is the
long form — the complete rule set and the controls that map to them.

This is intentionally rule-focused. Implementation notes (generators,
algorithms, file layout) live elsewhere.

## Shared conventions

All five games share the same chrome and the same control vocabulary,
so the rule sections below only mention game-specific deviations.

- **Difficulty** (Easy / Medium / Hard): controls how heavily the
  generator constrains the puzzle. The rules themselves never change.
- **Board size**: ranges and increments differ per game (see each
  section). Changing size always starts a fresh puzzle.
- **New Game**: regenerates a puzzle at the current difficulty and
  size, clearing the timer.
- **Reset**: clears everything the player has placed / drawn, but
  keeps the same puzzle.
- **Undo** (Queens, Tango, Sudoku): steps back through your recent
  moves — up to ~20, and a Reset counts as one step. `Ctrl`/`⌘`+`Z`
  also works. Cleared on New Game.
- **Reveal**: toggles a faint overlay of the intended solution.
  In the cell-toggle games (Queens, Tango, Sudoku) it shows a small
  hint glyph in the corner of each editable cell; in Zip it draws the
  canonical path under the player's line.
- **Timer**: starts on New Game / size / difficulty change; stops on
  win.
- **Violation feedback** (Queens, Tango, Sudoku): rule breaks are
  shown as red marks on the offending cells. Conflicts directly
  caused by your last move are debounced (so rapidly cycling a cell
  doesn't strobe red); unrelated conflicts remain visible
  immediately.
- **Win**: every game shows a "You Win!" badge in the status row and
  tints the placed symbols / path gold.

---

## Queens

**Goal.** Place exactly N queens on an N×N board so that every row,
every column, every coloured region, and every 8-cell neighbourhood
contains exactly one queen.

### Board

- N×N grid, with N from **5×5** to **12×12**.
- The board is partitioned into **N coloured regions** — irregular
  connected shapes that tile the whole board. Region colours are
  just labels; they have no other meaning.

### Rules

1. Each **row** contains exactly one queen.
2. Each **column** contains exactly one queen.
3. Each **coloured region** contains exactly one queen.
4. No two queens are **8-neighbours** (orthogonally OR diagonally
   adjacent). This is stricter than standard N-Queens, where queens
   attack along full diagonals — here only the immediately adjacent
   8 cells are forbidden, but queens on the same row/column still
   conflict (rules 1–2 cover that).

### Controls

- **Click a cell** to cycle through `empty → × → ♛ → empty`.
  - `×` is a personal "I think no queen goes here" marker. It is
    *not* a rule; the solver ignores it.
  - `♛` is an actual placement.
- **Drag** to bulk-toggle × marks:
  - Starting on an empty cell paints × onto every empty cell the
    pointer passes over (`♛` cells are left alone).
  - Starting on a × cell clears the × from every × the pointer
    passes over — including the starting cell. Releasing without
    ever leaving the starting cell falls back to a normal cycle,
    so a still tap on × still goes to `♛`.
- **Reveal (?)** draws a small grey queen in the top-left of every
  empty cell, showing the intended solution.

### Win

All N queens placed and no rule violated. There are no required
empty cells — finishing the board automatically satisfies all four
rules.

---

## Tango

**Goal.** Fill every cell of an N×N board with a sun (☀) or a moon
(☾) so that the row/column counts, the run-length, and the wall
constraints all hold.

### Board

- N×N grid, with N from **6×6**, **8×8**, **10×10** (N must be even
  so the half/half count works out).
- Some cells are **pre-filled** (slightly darker background) and
  cannot be changed.
- Some cell **boundaries** carry a wall glyph:
  - `=`  the two adjacent cells must contain the **same** symbol.
  - `×`  the two adjacent cells must contain **different** symbols.

### Rules

1. Each row contains exactly **N/2 suns and N/2 moons**.
2. Each column contains exactly **N/2 suns and N/2 moons**.
3. **No three identical symbols in a row** — neither three suns
   nor three moons may appear consecutively in any row or column.
4. Every `=` wall: the two cells it sits between must agree.
5. Every `×` wall: the two cells it sits between must differ.
6. Pre-filled cells cannot be modified.

### Controls

- **Click a cell** to cycle through `empty → ☀ → ☾ → empty`.
- **Reveal (?)** shows a small sun/moon hint in the top-left of
  every player-editable cell.

### Win

Every cell is filled and rules 1–5 all hold (rule 6 is enforced by
the input itself).

---

## Sudoku

**Goal.** Fill every cell of an N×N board with a digit from 1..N so
that each row, column, and box contains each digit exactly once.

### Board

- N×N grid, with N from **6×6**, **9×9**, or **12×12**.
- Boxes:
  - 6×6 → 2×3 boxes (2 rows × 3 cols of cells per box, giving
    3 boxes per row, 2 per column → six 2×3 boxes total).
  - 9×9 → 3×3 boxes (the classic Sudoku layout).
  - 12×12 → 3×4 boxes (3 rows × 4 cols per box). Digits run 1..12;
    10, 11, 12 are drawn hex-style as **A**, **B**, **C**.
- Some cells are **pre-filled** (locked, dark digits); the rest are
  empty.

### Rules

1. Each **row** contains every digit in 1..N exactly once.
2. Each **column** contains every digit in 1..N exactly once.
3. Each **box** contains every digit in 1..N exactly once.
4. Pre-filled digits cannot be modified.

### Controls

- **Select a cell** by clicking it. Same-row, same-column and
  same-box cells get a soft tint to help you spot conflicts; cells
  with the same digit as the selected one are tinted slightly more.
- **Arrow keys** move the selection.
- **Type a digit** (`1`–`9`, plus `A`–`C` for 10–12 on a 12×12) on
  the keyboard, or click a digit on the on-screen keypad, to fill
  the selected cell.
- **Backspace**, **Delete**, **0**, or **Erase** on the keypad
  clears a player-placed digit. Pre-filled digits are protected.
- **Notes mode** (`N` key, or the **Notes** button on the keypad):
  digits you enter go in as small **pencil marks** in a sub-grid
  arranged in the same shape as a box. Toggle the digit again to
  remove it from the notes. Entering a real digit while a cell has
  notes wipes the notes for that cell.
- **Reveal (?)** shows a small green digit in the top-left of every
  player-editable cell — the intended solution.

### Win

Every cell is filled and rules 1–3 all hold (rule 4 is enforced by
the input).

---

## Zip

**Goal.** Draw a single continuous path that visits every open cell
exactly once, passing through the numbered checkpoints **in
numerical order**.

### Board

- N×N grid, with N from **5×5** to **12×12**.
- **Holes** (grey cells): unreachable. The path may never enter
  them. (The current generator produces hole-free boards, so in
  practice every cell is open.)
- **Walls** (thick black segments on cell borders): the path may
  never cross one.
- **Checkpoints** (numbered circles): K cells are labelled
  `1, 2, …, K`. They sit on open cells.

### Rules

1. The path is a sequence of orthogonally-adjacent (4-neighbour)
   cells; diagonals are not allowed.
2. The path **covers every open cell exactly once** (i.e. a
   Hamiltonian path over the set of open cells).
3. The path **starts at the cell labelled 1**.
4. The path **ends at the highest-numbered checkpoint** (`K`).
5. The path visits the checkpoints in order: `1 → 2 → 3 → … → K`.
   Non-checkpoint cells may appear between checkpoints in any
   arrangement, as long as the numbered ones still appear in order.
6. The path may not pass through a hole or cross a wall.

### Controls

- **Press and drag** with the mouse (or finger) to draw.
  - From an empty state, the drag must start on cell `1`.
  - Otherwise, the drag must start on a cell that is already on
    the path. Doing so **truncates** the path back to that cell
    (anything drawn after it is dropped).
- While dragging the head, moving onto an adjacent open cell
  **extends** the path. Moving onto the cell immediately *before*
  the head **retracts** by one step. Moving onto any other cell on
  the existing path during a drag does nothing — that protects you
  from accidentally lopping off long sections.
- Releasing keeps the current state. To rewind further or to start
  over, release and press again on the cell you want to continue
  from.
- Trying to cross a wall, enter a hole, or reach a non-adjacent
  cell briefly flashes the offending cell red.
- **Reveal (?)** draws the canonical solution path as a faint green
  line under your own.
- **Hint (💡)** either spotlights the stretch of your path that has
  left the unique solution — dimming every other cell so you can see
  how far to retrace — or, if you're still on track, draws a green
  connector to the next step(s). Press again to dismiss.
- **Undo (↶ / Ctrl+Z)** steps back one drag gesture at a time (up to
  20). Reset is undoable too, until you win.

### Mistake feedback

You're allowed to visit a checkpoint with the wrong number, but the
path from that checkpoint onward is highlighted red (cell tint plus
red path stroke that picks up where the blue gradient left off).
The win check requires the order to be correct, so you'll need to
retract back past the offending checkpoint to clear the red.

The path **head** also turns red when you run *past* the final
checkpoint, or park on it before every cell is covered — both are
dead ends you must back out of.

### Win

The path covers every open cell, visits the checkpoints in order,
and ends at checkpoint `K`.

---

## Patches

**Goal.** Cover the whole N×N board with non-overlapping rectangles —
exactly one per clue — where each rectangle matches its clue's shape
(and size, if the clue gives one).

### Board

- N×N grid, with N from **5×5** to **12×12**.
- Most cells are blank. A few carry a **clue** glyph; each clue is the
  seed of exactly one rectangle. The glyph states the required shape:
  - **Square** — the rectangle must be a square (width = height).
  - **Wide** — wider than tall (width > height).
  - **Tall** — taller than wide (height > width).
  - **Any** (dashed composite glyph) — any rectangle shape.
- If the glyph also shows a **number**, the rectangle's **area** must
  equal it (e.g. `6` → 1×6, 2×3, 3×2 or 6×1, subject to the shape). No
  number means any size.
- Each clue (and its rectangle) has its own colour; blank cells are
  neutral until a rectangle is drawn over them.

### Rules

1. Every clue is covered by exactly **one** rectangle, and every
   rectangle contains exactly **one** clue (a one-to-one pairing).
2. Each rectangle satisfies its clue's **shape** (square / wide / tall
   / any).
3. If the clue carries a **number**, the rectangle's area equals it.
4. **No 1×1 rectangles** — every rectangle covers at least two cells.
5. Rectangles **never overlap**.
6. The rectangles **fill the whole board** — no cell left uncovered.

### Controls

- **Drag from a blank cell** to draw a rectangle. A grey preview grows
  toward the pointer (within one gesture it only ever grows). When it
  covers exactly one clue it tints to that clue's colour; the drag
  refuses to grow so that it would cover a **second** clue or **overlap
  an existing rectangle**.
- **Release**:
  - preview covering **no** clue → discarded (nothing placed);
  - preview covering **one** clue → placed.
  - Shortly after placing, a rectangle that already breaks its clue
    (too big for the stated size, or a shape it can no longer become)
    flashes **red** with a small bubble explaining why.
- **Drag from inside a placed rectangle** to resize it — grow-only;
  releasing replaces the old rectangle.
- **Click a placed rectangle** (a tap, no drag) to remove it.
- Each placed rectangle shows a small **size badge** (current W×H).
- **Hint**: highlights the next deduction (conflict-first, then the
  forced placement / cell). Press again to dismiss.
- **Reveal (?)**: shows the intended solution rectangles.

### Win

Every clue owns one valid rectangle and the rectangles tile the grid
with no gaps or overlaps.
