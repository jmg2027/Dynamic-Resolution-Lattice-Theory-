import E213.Meta.Nat.PureNat
import E213.Meta.Nat.UnitList

/-!
# UnitGrid — the rung-2 birthplace of `×`-commutativity: the grid transpose

`UnitList` showed `+`-commutativity is born from **append** on a 1-D list
of indistinguishable units: counting forgets arrangement, and what
survives the forgetting commutes (`UnitList.add_comm_from_append`).

This file is the level-2 sibling.  Where the 1-D unit list gives `+`,
the 2-D unit **grid** gives `×`.  An `a × b` grid of indistinguishable
units — `a` rows, each of length `b` — has a total cell count.  Counting
it **row by row** reads off `a * b`.  Counting the **transpose** — the
same cells re-laid as `b` columns of height `a` — reads off `b * a`.
The two counts are of the *same units*, so they agree, and
`a * b = b * a` falls out **without** ever assuming `Nat.mul_comm`.

Derived from list induction alone, no multiplicative algebra remembered:

* `total` is the cell-count of a grid (sum of row lengths);
* `rows a b` is the canonical uniform grid (`a` rows of `b` units);
* row-count: `total (rows a b) = a * b` (`total_rows`★);
* `heads`/`tails` peel the **first column** off a grid (one unit from
  every non-empty row); the peel preserves the count, re-distributed:
  `count (heads g) + total (tails g) = total g`
  (`heads_tails_total`★, the crux) — the cell that leaves a row enters
  the column, nothing is lost or invented, proved by bare induction
  because indistinguishable cells carry no position to permute;
* `transpose b` iterates the column-peel `b` times, turning the `b`
  columns into the `b` rows of the transpose;
* the transpose of `rows a b` is `rows b a` (`transpose_rows`★):
  `b` columns of height `a`;
* transpose preserves the total cell count
  (`total_transpose_rows`★, the geometric double-count);
* compose: `a * b = total (rows a b) = total (transpose b (rows a b))
  = total (rows b a) = b * a` (`mul_comm_from_grid`★★).

The genuine double-count lives in `heads_tails_total` /
`total_transpose_rows`: row-counting (`total_rows`) and column-counting
(transpose, then `total_rows` again at the swapped dimensions) are two
*different* recursions over the same cells, and their equality is the
load-bearing transpose lemma — never `Nat.mul_comm` in disguise.

All ∅-axiom; self-contained inductions (no core `List` lemmas, no
`mul_comm`).
-/

namespace E213.Meta.Nat.UnitGrid

open E213.Meta.Nat.UnitList (count fromNat count_fromNat)

/-- A grid: a list of rows, each row a list of indistinguishable units. -/
abbrev UGrid := List (List Unit)

/-- The total cell count of a grid: sum of the per-row unit counts. -/
def total : UGrid → Nat
  | [] => 0
  | r :: g => count r + total g

/-- `replicate n x`: `n` copies of `x` (bare recursion, no core lemma). -/
def replicate {α : Type} : Nat → α → List α
  | 0,     _ => []
  | n + 1, x => x :: replicate n x

/-- The canonical `a × b` uniform grid: `a` rows, each a `b`-unit row. -/
def rows (a b : Nat) : UGrid := replicate a (fromNat b)

/-- A grid of `a` empty rows has no cells. -/
theorem total_rows_zero : ∀ (a : Nat), total (rows a 0) = 0
  | 0     => rfl
  | a + 1 => by
      show total (fromNat 0 :: replicate a (fromNat 0)) = 0
      show count ([] : List Unit) + total (replicate a (fromNat 0)) = 0
      show 0 + total (replicate a (fromNat 0)) = 0
      rw [Nat.zero_add]; exact total_rows_zero a

/-- ★ Row-count: a grid of `a` rows of `b` units totals `a * b`.
    Counting row by row — each row contributes `count (fromNat b) = b`. -/
theorem total_rows : ∀ (a b : Nat), total (rows a b) = a * b
  | 0,     b => by
      show total (replicate 0 (fromNat b)) = 0 * b
      rw [Nat.zero_mul]; rfl
  | a + 1, b => by
      show total (fromNat b :: replicate a (fromNat b)) = (a + 1) * b
      show count (fromNat b) + total (replicate a (fromNat b)) = (a + 1) * b
      have ih : total (replicate a (fromNat b)) = a * b := total_rows a b
      rw [count_fromNat, ih, Nat.succ_mul, Nat.add_comm]

/-! ### The column-peel

`heads` collects the first unit of every non-empty row (= the first
column).  `tails` drops it.  Together they re-partition the grid's cells:
one cell from each non-empty row moves into the column, the rest stay. -/

/-- The first column: the head unit of every non-empty row. -/
def heads : UGrid → List Unit
  | [] => []
  | [] :: g => heads g
  | (u :: _) :: g => u :: heads g

/-- Drop the first column: the tail of every row, empty rows dropped. -/
def tails : UGrid → UGrid
  | [] => []
  | [] :: g => tails g
  | (_ :: r) :: g => r :: tails g

/-- Pure Nat regroup used in the column-peel step (no `mul`).
    `(x+1) + (s+t) = (s+1) + (x+t)` — both sides are `x + s + t + 1`. -/
theorem regroup (x s t : Nat) : (x + 1) + (s + t) = (s + 1) + (x + t) :=
  calc (x + 1) + (s + t)
      = x + (s + (t + 1)) := by
        rw [Nat.add_assoc x 1 (s + t), Nat.add_comm 1 (s + t), Nat.add_assoc s t 1]
    _ = (s + 1) + (x + t) := by
        rw [Nat.add_comm t 1, ← Nat.add_assoc s 1 t,
            Nat.add_comm (s + 1) t, ← Nat.add_assoc x t (s + 1),
            Nat.add_comm (x + t) (s + 1)]

/-- ★ **Column-peel preserves the count** (the crux): the cells leaving
    the rows (`heads`) plus the cells that remain (`tails`) total the
    original grid — nothing is lost or invented when a column is peeled,
    because units are indistinguishable.  Bare induction. -/
theorem heads_tails_total : ∀ (g : UGrid),
    count (heads g) + total (tails g) = total g
  | [] => rfl
  | [] :: g => by
      show count (heads g) + total (tails g) = count ([] : List Unit) + total g
      show count (heads g) + total (tails g) = 0 + total g
      rw [Nat.zero_add]; exact heads_tails_total g
  | (u :: r) :: g => by
      show count (u :: heads g) + total (r :: tails g)
            = count (u :: r) + total g
      show (count (heads g) + 1) + (count r + total (tails g))
            = (count r + 1) + total g
      rw [regroup (count (heads g)) (count r) (total (tails g))]
      rw [heads_tails_total g]

/-! ### Transpose

A uniform `a × b` grid has exactly `b` columns.  `transpose b g` peels
those `b` columns off in turn, each becoming a row of the transpose, so
`transpose b (rows a b) = rows b a`.  The fuel `b` is the number of
columns, making the recursion structural. -/

/-- Peel `n` columns off a grid, collecting each as a row of the
    transpose.  For a uniform `a × b` grid use `n = b`. -/
def transpose : Nat → UGrid → UGrid
  | 0,     _ => []
  | n + 1, g => heads g :: transpose n (tails g)

/-- `heads` of a uniform `a × (b+1)` grid is a full column: one unit per
    row, `count = a`. -/
theorem heads_rows_succ : ∀ (a b : Nat),
    heads (rows a (b + 1)) = fromNat a
  | 0,     _ => rfl
  | a + 1, b => by
      show heads (fromNat (b + 1) :: replicate a (fromNat (b + 1))) = fromNat (a + 1)
      show heads ((() :: fromNat b) :: replicate a (fromNat (b + 1)))
            = () :: fromNat a
      show () :: heads (replicate a (fromNat (b + 1))) = () :: fromNat a
      exact congrArg (() :: ·) (heads_rows_succ a b)

/-- `tails` of a uniform `a × (b+1)` grid is the uniform `a × b` grid:
    every row loses its head unit. -/
theorem tails_rows_succ : ∀ (a b : Nat),
    tails (rows a (b + 1)) = rows a b
  | 0,     _ => rfl
  | a + 1, b => by
      show tails (fromNat (b + 1) :: replicate a (fromNat (b + 1))) = rows (a + 1) b
      show tails ((() :: fromNat b) :: replicate a (fromNat (b + 1)))
            = fromNat b :: replicate a (fromNat b)
      show fromNat b :: tails (replicate a (fromNat (b + 1)))
            = fromNat b :: replicate a (fromNat b)
      exact congrArg (fromNat b :: ·) (tails_rows_succ a b)

/-- ★ **The transpose of `rows a b` is `rows b a`**: peeling the `b`
    columns of an `a × b` grid yields `b` rows of height `a`. -/
theorem transpose_rows : ∀ (a b : Nat),
    transpose b (rows a b) = rows b a
  | _, 0     => rfl
  | a, b + 1 => by
      show heads (rows a (b + 1)) :: transpose b (tails (rows a (b + 1)))
            = rows (b + 1) a
      rw [heads_rows_succ a b, tails_rows_succ a b, transpose_rows a b]
      rfl

/-- ★ **Transpose preserves the total cell count** for uniform grids:
    each peeled column (`heads`) becomes a transpose row, and the
    column-peel never loses or invents a cell (`heads_tails_total`).
    This is the geometric double-count — the same units, recounted by
    columns.  Induction on the column index `b`. -/
theorem total_transpose_rows : ∀ (a b : Nat),
    total (transpose b (rows a b)) = total (rows a b)
  | a, 0     => by
      show total (transpose 0 (rows a 0)) = total (rows a 0)
      show total ([] : UGrid) = total (rows a 0)
      rw [total_rows_zero a]; rfl
  | a, b + 1 => by
      show total (heads (rows a (b + 1)) :: transpose b (tails (rows a (b + 1))))
            = total (rows a (b + 1))
      show count (heads (rows a (b + 1)))
            + total (transpose b (tails (rows a (b + 1))))
            = total (rows a (b + 1))
      rw [tails_rows_succ a b, total_transpose_rows a b]
      have h := heads_tails_total (rows a (b + 1))
      rw [tails_rows_succ a b] at h
      exact h

/-- ★★ **Multiplication commutes because the grid does**: counting the
    `a × b` unit grid by rows gives `a * b`; counting its transpose
    (`b` columns of height `a`) by rows gives `b * a`; the transpose is
    the same units, so the two counts agree.  No `Nat.mul_comm`. -/
theorem mul_comm_from_grid (a b : Nat) : a * b = b * a :=
  calc a * b
      = total (rows a b)              := (total_rows a b).symm
    _ = total (transpose b (rows a b)) := (total_transpose_rows a b).symm
    _ = total (rows b a)             := by rw [transpose_rows a b]
    _ = b * a                        := total_rows b a

end E213.Meta.Nat.UnitGrid
