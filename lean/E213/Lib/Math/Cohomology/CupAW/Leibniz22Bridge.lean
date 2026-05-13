import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22Alpha

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# (5, 2, 2) Cup AW Leibniz Universal — bz5_2 ↔ basis/zero bridge

bz5_2 reduces to either Cochain.zero (when β k = false) or
basis 5 2 k (when β k = true).  This file proves the bridge
function rewrites + the per-component cases that feed into
both lenses.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Lib.Math.Cohomology.CupAW.Zero (cupAW_zero_left cupAW_zero_right delta_zero)

/-- Pointwise (PURE): bz5_2 β k j = false (= Cochain.zero 5 2 j)
    when β k = false.  Companion to the funext-based `bz5_2_false`. -/
theorem bz5_2_false_at (β : Cochain 5 2) (k : Fin 10)
    (hβ : β k = false) (j : Fin 10) :
    bz5_2 β k j = Cochain.zero 5 2 j := by
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- Pointwise (PURE): bz5_2 β k j = basis 5 2 k j when β k = true. -/
theorem bz5_2_true_at (β : Cochain 5 2) (k : Fin 10)
    (hβ : β k = true) (j : Fin 10) :
    bz5_2 β k j = basis 5 2 k j := by
  show ((k.val == j.val) && β k) = basis 5 2 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

end E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge
