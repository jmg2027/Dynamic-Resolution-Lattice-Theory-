/-!
# Zigzag / Euler up-down numbers via the boustrophedon (Seidel) triangle

The zigzag numbers `A(n)` (OEIS A000111: 1,1,1,2,5,16,61,272,1385,...) count the
alternating permutations of `{1,…,n}`.  They are read off the **boustrophedon
(Seidel) triangle** `T(n,k)`:

  `T(0,0) = 1`,  `T(n,0) = 0` for `n ≥ 1`,
  `T(n,k) = T(n,k−1) + T(n−1, n−k)`   (the boustrophedon fill),
  `A(n) = T(n,n)`.

The triangle entry `T(n,k)` is computed by a fuel-based recursion (plain
structural recursion on fuel → PURE).  The recursion depth of `T(n,n)` is the
triangular number `n(n+1)/2`, so the fuel `n·n+n ≥ n(n+1)/2` always suffices.
-/

namespace E213.Lib.Math.Combinatorics.ZigzagNumbers

/-- Fuel-based boustrophedon triangle entry.  `tF fuel n k = T n k` whenever
    `fuel` is at least the recursion depth at `(n,k)`.  The two recursive calls
    are `T(n,k−1)` (same row, one fewer column) and `T(n−1, n−k)` (previous row,
    column `n−k`); fuel decreases by one each call → plain structural recursion. -/
def tF : Nat → Nat → Nat → Nat
  | _,     0,     0     => 1
  | _,     _ + 1, 0     => 0
  | 0,     _,     _ + 1 => 0
  | f + 1, n,     k + 1 => tF f n k + tF f (n - 1) (n - (k + 1))

/-- Boustrophedon triangle entry at full fuel. -/
def zigzagT (n k : Nat) : Nat := tF (n * n + n) n k

/-- Zigzag / Euler up-down number `A(n) = T(n,n)`. -/
def zigzag (n : Nat) : Nat := zigzagT n n

/-- ★ **Boustrophedon fill recurrence (fuel form)**: at positive fuel and column,
    `tF (f+1) n (k+1) = tF f n k + tF f (n−1) (n−(k+1))` — the two recursive calls
    of the triangle fill (same row, previous column) and (previous row, mirrored
    column).  True by `rfl` (it is the defining equation of `tF`). -/
theorem zigzag_rec (f n k : Nat) :
    tF (f + 1) n (k + 1) = tF f n k + tF f (n - 1) (n - (k + 1)) := by rw [tF]

/-- Boustrophedon boundary: `T(0,0) = 1` (the apex of the triangle). -/
theorem zigzagT_apex : zigzagT 0 0 = 1 := rfl

/-- `zigzag_table` — `A(0..8) = 1,1,1,2,5,16,61,272,1385` (A000111), by `decide`. -/
theorem zigzag_table :
    zigzag 0 = 1
    ∧ zigzag 1 = 1
    ∧ zigzag 2 = 1
    ∧ zigzag 3 = 2
    ∧ zigzag 4 = 5
    ∧ zigzag 5 = 16
    ∧ zigzag 6 = 61
    ∧ zigzag 7 = 272
    ∧ zigzag 8 = 1385 := by
  decide

/-- ★ **Boustrophedon entry recurrence (table form)**: the triangle fill
    `T(n,k+1) = T(n,k) + T(n−1, n−1−k)` verified on the concrete entries
    `zigzagT` for rows `n = 1..5`, all columns.  (At these entries the two fuel
    values `n·n+n` both exceed the recursion depth, so the entry-level recurrence
    holds even though the per-call fuel differs; checked by `decide`.) -/
theorem zigzag_entry_rec_table :
    -- row 1
    zigzagT 1 1 = zigzagT 1 0 + zigzagT 0 0
    -- row 2
    ∧ zigzagT 2 1 = zigzagT 2 0 + zigzagT 1 1
    ∧ zigzagT 2 2 = zigzagT 2 1 + zigzagT 1 0
    -- row 3
    ∧ zigzagT 3 1 = zigzagT 3 0 + zigzagT 2 2
    ∧ zigzagT 3 2 = zigzagT 3 1 + zigzagT 2 1
    ∧ zigzagT 3 3 = zigzagT 3 2 + zigzagT 2 0
    -- row 4
    ∧ zigzagT 4 1 = zigzagT 4 0 + zigzagT 3 3
    ∧ zigzagT 4 2 = zigzagT 4 1 + zigzagT 3 2
    ∧ zigzagT 4 3 = zigzagT 4 2 + zigzagT 3 1
    ∧ zigzagT 4 4 = zigzagT 4 3 + zigzagT 3 0
    -- row 5
    ∧ zigzagT 5 1 = zigzagT 5 0 + zigzagT 4 4
    ∧ zigzagT 5 2 = zigzagT 5 1 + zigzagT 4 3
    ∧ zigzagT 5 3 = zigzagT 5 2 + zigzagT 4 2
    ∧ zigzagT 5 4 = zigzagT 5 3 + zigzagT 4 1
    ∧ zigzagT 5 5 = zigzagT 5 4 + zigzagT 4 0 := by
  decide

/-- `zigzag n = zigzagT n n = T(n,n)`: the zigzag number is the right-hand
    (return) endpoint of boustrophedon row `n`.  True by definition (`rfl`). -/
theorem zigzag_eq_diag (n : Nat) : zigzag n = zigzagT n n := rfl

end E213.Lib.Math.Combinatorics.ZigzagNumbers
