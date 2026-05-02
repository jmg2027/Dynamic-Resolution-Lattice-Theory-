import E213.Math.Cohomology.CupAW.LeibnizAlgLift22
import E213.Math.Cohomology.CupAW.LeibnizAlgLift22Alpha

/-!
# (5, 2, 2) Cup AW Leibniz Universal — bz5_2 ↔ basis/zero bridge

bz5_2 reduces to either Cochain.zero (when β k = false) or
basis 5 2 k (when β k = true).  This file proves the bridge
function rewrites + the per-component cases that feed into
both lenses.
-/

namespace E213.Math.Cohomology.CupAW.Leibniz22Bridge

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.Core (cupAW)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Math.Cohomology.CupAW.Zero (cupAW_zero_left cupAW_zero_right delta_zero)

/-- bz5_2 with β k = false reduces to Cochain.zero. -/
theorem bz5_2_false (β : Cochain 5 2) (k : Fin 10)
    (hβ : β k = false) :
    bz5_2 β k = Cochain.zero 5 2 := by
  funext j
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- bz5_2 with β k = true reduces to basis 5 2 k. -/
theorem bz5_2_true (β : Cochain 5 2) (k : Fin 10)
    (hβ : β k = true) :
    bz5_2 β k = basis 5 2 k := by
  funext j
  show ((k.val == j.val) && β k) = basis 5 2 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

/-- Function-level zero collapse helpers. -/
theorem cupAW_zero_left_fn (n a b : Nat) (β : Cochain n b) :
    cupAW n a b (Cochain.zero n a) β = Cochain.zero n (a + b - 1) := by
  funext τ; exact cupAW_zero_left _ _ _ _ _

theorem cupAW_zero_right_fn (n a b : Nat) (α : Cochain n a) :
    cupAW n a b α (Cochain.zero n b) = Cochain.zero n (a + b - 1) := by
  funext τ; exact cupAW_zero_right _ _ _ _ _

theorem delta_zero_fn (n k : Nat) :
    delta (Cochain.zero n k) = Cochain.zero n (k + 1) := by
  funext τ; exact delta_zero _ _ _

end E213.Math.Cohomology.CupAW.Leibniz22Bridge
