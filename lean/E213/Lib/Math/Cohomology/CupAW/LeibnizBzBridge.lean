import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.Cochain.V5_3Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz

/-!
# CupAW bz5_<n> bridge — pointwise reductions for n ∈ {1, 2, 3}

For each `bz5_<n> β k` (the basis-zero decomposition at stratum
`(5, n)`), this file provides the two pointwise PURE companions:

  · `bz5_<n>_false_at`: `bz5_<n> β k j = Cochain.zero 5 <n> j`
    when `β k = false`
  · `bz5_<n>_true_at`:  `bz5_<n> β k j = basis 5 <n> k j`
    when `β k = true`

Used in the per-α (resp. per-β) component case-split for
`(5, n, _)` AW Leibniz universal lifts.

The three strata share the identical proof template (Bool
case-split on `(k.val == j.val) && β k`); collected here in one
file for the (5, 1) / (5, 2) / (5, 3) instances.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.V5_1DecompR (bz5_1)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Lib.Math.Cohomology.Cochain.V5_3Decomp (bz5_3)

/-! ### §1 — `bz5_1` at stratum (5, 1) -/

/-- Pointwise (PURE): `bz5_1 β k j = false` when `β k = false`. -/
theorem bz5_1_false_at (β : Cochain 5 1) (k : Fin 5)
    (hβ : β k = false) (j : Fin 5) :
    bz5_1 β k j = Cochain.zero 5 1 j := by
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- Pointwise (PURE): `bz5_1 β k j = basis 5 1 k j` when `β k = true`. -/
theorem bz5_1_true_at (β : Cochain 5 1) (k : Fin 5)
    (hβ : β k = true) (j : Fin 5) :
    bz5_1 β k j = basis 5 1 k j := by
  show ((k.val == j.val) && β k) = basis 5 1 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

/-! ### §2 — `bz5_2` at stratum (5, 2) -/

/-- Pointwise (PURE): `bz5_2 β k j = false` when `β k = false`. -/
theorem bz5_2_false_at (β : Cochain 5 2) (k : Fin 10)
    (hβ : β k = false) (j : Fin 10) :
    bz5_2 β k j = Cochain.zero 5 2 j := by
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- Pointwise (PURE): `bz5_2 β k j = basis 5 2 k j` when `β k = true`. -/
theorem bz5_2_true_at (β : Cochain 5 2) (k : Fin 10)
    (hβ : β k = true) (j : Fin 10) :
    bz5_2 β k j = basis 5 2 k j := by
  show ((k.val == j.val) && β k) = basis 5 2 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

/-! ### §3 — `bz5_3` at stratum (5, 3) -/

/-- Pointwise (PURE): `bz5_3 β k j = false` when `β k = false`. -/
theorem bz5_3_false_at (β : Cochain 5 3) (k : Fin 10)
    (hβ : β k = false) (j : Fin 10) :
    bz5_3 β k j = Cochain.zero 5 3 j := by
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- Pointwise (PURE): `bz5_3 β k j = basis 5 3 k j` when `β k = true`. -/
theorem bz5_3_true_at (β : Cochain 5 3) (k : Fin 10)
    (hβ : β k = true) (j : Fin 10) :
    bz5_3 β k j = basis 5 3 k j := by
  show ((k.val == j.val) && β k) = basis 5 3 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

end E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
