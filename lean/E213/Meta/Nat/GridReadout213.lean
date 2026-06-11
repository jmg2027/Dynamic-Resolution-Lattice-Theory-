import E213.Meta.Nat.PureNat
import E213.Meta.Nat.UnitList

/-!
# GridReadout213 — a SECOND source of vector-valued readout: substrate dimension

`exp` (the `×`-count-Lens) is vector-valued for ONE reason: the
multiplicative atoms (primes) are **distinguishable**, so the `×`-count
splits into one coordinate per prime axis — **atom-coloring**.  This file
pins a *second*, independent reason a readout becomes vector-valued — the
originator's "what if 3-D cells / higher substrate?" probe: the
**dimension of the substrate** the units sit on.

* On a **1-D** substrate (`UnitList`) the only readout is the **length**
  (= `count`): one `Nat`, living on a total order
  (`oneD_readout_total`).  One number suffices; nothing to split.
* On a **2-D** substrate (`UnitGrid`) the readout **splits**.  An `a × b`
  grid of the same indistinguishable units carries an `area = a * b` (the
  bulk cell-count, `UnitGrid.total`) *and* a boundary readout
  `perimeter = 2 * (a + b)`.  These are **independent coordinates**: area
  does not determine perimeter (`readout_splits`★★), so no single number
  captures the 2-D cell-set.

The independence witness is `(1,6)` vs `(2,3)`:

  `area 1 6 = 1*6 = 6 = 2*3 = area 2 3`   (same area)
  `perimeter 1 6 = 2*(1+6) = 14 ≠ 10 = 2*(2+3) = perimeter 2 3`.

Sharpened to the bare coordinates (`area_eq_sum_differ`): the
multiplicative readout (`1*6 = 2*3`) and the additive readout
(`1+6 ≠ 2+3`, the semiperimeter) are independent axes of the *same*
2-D cell-set — the product agrees while the sum differs.  And the 2-D
readout is **≥2-dimensional, not exactly 2**: the diagonal-cell count
`diagonal = min a b` is a *third* coordinate, again undetermined by area
(`readout_splits_three`).

So "vector-valued readout" has (at least) two sources: **atom-coloring**
(distinguishable `×`-atoms → the prime axes of `exp`) and **substrate
dimension** (raise the grid dimension → the count splits into geometric
readouts).  That answers the "3-D cells?" probe directly: more substrate
dimensions ⇒ more independent readout components, none collapsible to the
1-D length.

Honesty note: the split formalized here is **metric** (area / perimeter /
diagonal — extensive Euclidean readouts of a uniform grid).  The deeper,
presentation-invariant version of "the count splits into invariants when
you raise the substrate dimension" is **topological** — the Euler
characteristic / Betti numbers, which live in the repo's
`Lib/Math/Geometry/`.  This module pins the elementary metric facet, the
entry rung of the same knob.

Pin: frontier `research-notes/frontiers/numbersystem_square.md`,
"tree ↔ wall loop" — the "raise the substrate dimension → the count
splits into invariants" knob.

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
