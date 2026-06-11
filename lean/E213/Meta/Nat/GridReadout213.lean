import E213.Meta.Nat.PureNat
import E213.Meta.Nat.UnitList

/-!
# GridReadout213 — substrate dimension and the readout split (corrected: see `Shape213`)

The originator's "what if 3-D cells / higher substrate?" probe.  An `a × b`
grid of indistinguishable units carries an internal `area = a * b` (the
bulk cell-count, `UnitGrid.total`).  This file also records a `perimeter`
readout and shows area does not determine it — but **`perimeter` is not
internal**: an abstract unit-grid has no boundary; `perimeter = 2*(a+b)`
imports the **Euclidean embedding** of the rectangle in the plane.  So the
perimeter-based `readout_splits` is a *metric/imported* witness, kept here
only as the entry rung; the **import-free** statement lives in `Shape213`,
where the honest internal readout is the **shape** `(a,b)` itself (which
already distinguishes `1×6` from `2×3` with no boundary needed).

**Correction (originator catch).**  `perimeter` made it *look* as if
substrate dimension were a **second, independent** source of vector-valued
readout besides atom-coloring (`exp`).  It is not.  The internal readout is
the shape = an **ordered factorization**; `area` is its product-collapse;
the **dimension = the number of factors**.  A `d`-grid is a `d`-factor
factorization, and the prime factorization (`exp`, `VpMul`) is the
**maximal-dimension** one — so substrate dimension and atom-coloring are
**ONE structure** (the ×-atom / factorization) at different resolutions,
not two independent sources.  See `Shape213` for the corrected, import-free
formalization, and `numbersystem_square.md` "tree ↔ wall loop".

What survives here (all true, all ∅-axiom):
* `oneD_readout_total` — the 1-D substrate has a single readout (length) on
  a total order;
* `area` / `readout_splits` — area does not determine the perimeter readout
  (witness `(1,6)` vs `(2,3)`, area `6`, perimeter `14 ≠ 10`), with the
  caveat above that `perimeter` is the imported reading;
* `area_eq_sum_differ`, `diagonal` / `readout_splits_three` — further
  metric readouts, likewise imported dressings of the internal shape.

All ∅-axiom: witnesses closed by `decide` / `rfl` on concrete `Nat`, and
the 1-D total-order lemma by bare `Nat` induction.
-/

namespace E213.Meta.Nat.GridReadout213

open E213.Meta.Nat.UnitList (count fromNat)

/-! ### The two readouts of a 2-D cell-set -/

/-- The **area** readout of an `a × b` grid: the bulk cell count `a * b`.
    This is exactly the number `UnitGrid` reads off the uniform grid by
    its row/column double-count (`E213.Meta.Nat.UnitGrid.total_rows`):
    the multiplicative readout. -/
def area (a b : Nat) : Nat := a * b

/-- The **perimeter** readout of an `a × b` grid: the boundary cell count
    `2 * (a + b)`.  A *second* readout of the same cell-set, reading off
    the boundary rather than the bulk. -/
def perimeter (a b : Nat) : Nat := 2 * (a + b)

/-! ### ★★ The split: area does NOT determine perimeter -/

/-- ★★ **The 2-D readout splits into independent components**: two
    distinct `a × b` cell-sets can have **equal area** yet **unequal
    perimeter**, so the area readout does *not* determine the boundary
    readout — no single number captures the 2-D cell-set.  Witness:
    `(1,6)` vs `(2,3)`, area `1*6 = 2*3 = 6`, perimeter
    `2*(1+6) = 14 ≠ 10 = 2*(2+3)`. -/
theorem readout_splits :
    ∃ a b c d, area a b = area c d ∧ perimeter a b ≠ perimeter c d :=
  ⟨1, 6, 2, 3, by decide, by decide⟩

/-- ★ The sharpened **bare form** of the split: on the witness `(1,6)` vs
    `(2,3)` the multiplicative readout (area) **agrees** while the
    additive readout (semiperimeter `a + b`) **differs** — the product and
    the sum are independent coordinates of the same 2-D cell-set. -/
theorem area_eq_sum_differ : (1 * 6 = 2 * 3) ∧ (1 + 6 ≠ 2 + 3) := by
  decide

/-! ### ★ Contrast with the 1-D substrate: a single, totally-ordered readout -/

/-- ★ **The 1-D readout is a single number on a total order.**  A
    `UnitList`'s only readout is its length (= `count`), one `Nat`, and
    any two `Nat` readouts are comparable: `m ≤ n ∨ n ≤ m`.  One number
    suffices on the 1-D substrate; there is no second coordinate to read,
    in contrast with the 2-D pair `(area, perimeter)` which does NOT
    collapse to one (`readout_splits`).  Proved by bare `Nat` induction
    (no core total-order lemma, kept ∅-axiom). -/
theorem oneD_readout_total : ∀ m n : Nat, m ≤ n ∨ n ≤ m
  | 0,     _     => Or.inl (Nat.zero_le _)
  | _ + 1, 0     => Or.inr (Nat.zero_le _)
  | m + 1, n + 1 =>
      match oneD_readout_total m n with
      | Or.inl h => Or.inl (Nat.succ_le_succ h)
      | Or.inr h => Or.inr (Nat.succ_le_succ h)

/-- The 1-D readout the order above lives on, spelled out as the unit-list
    length: `count (fromNat n) = n`.  The single readout of the 1-D
    substrate, re-exposed here as the contrast point. -/
theorem oneD_readout_is_length (n : Nat) : count (fromNat n) = n :=
  E213.Meta.Nat.UnitList.count_fromNat n

/-! ### The 2-D readout is ≥2-dimensional, not exactly 2 -/

/-- A **third** readout of an `a × b` grid: the diagonal-cell count
    `min a b` (the longest main diagonal that fits — the grid's
    staircase).  Another extensive coordinate, distinct from area and
    perimeter. -/
def diagonal (a b : Nat) : Nat := Nat.min a b

/-- ★ The 2-D readout is **≥2-dimensional, not exactly 2**: even fixing
    the area, the diagonal count is still free.  Witness again `(1,6)` vs
    `(2,3)`: area `6 = 6`, but `min 1 6 = 1 ≠ 2 = min 2 3`.  Together with
    `readout_splits`, `(area, perimeter, diagonal)` are three genuinely
    independent readouts of the 2-D cell-set. -/
theorem readout_splits_three :
    ∃ a b c d, area a b = area c d ∧ diagonal a b ≠ diagonal c d :=
  ⟨1, 6, 2, 3, by decide, by decide⟩

end E213.Meta.Nat.GridReadout213
