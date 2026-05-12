import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha
import E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
/-!
# bz5_1 ↔ basis/zero rewrite for (5, 2, 1) lift
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz21Bridge

open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cochain.V5_1DecompR (bz5_1)

/-- Pointwise (PURE): bz5_1 β k j = false (= Cochain.zero 5 1 j)
    when β k = false. -/
theorem bz5_1_false_at (β : Cochain 5 1) (k : Fin 5)
    (hβ : β k = false) (j : Fin 5) :
    bz5_1 β k j = Cochain.zero 5 1 j := by
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- Pointwise (PURE): bz5_1 β k j = basis 5 1 k j when β k = true. -/
theorem bz5_1_true_at (β : Cochain 5 1) (k : Fin 5)
    (hβ : β k = true) (j : Fin 5) :
    bz5_1 β k j = basis 5 1 k j := by
  show ((k.val == j.val) && β k) = basis 5 1 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

end E213.Lib.Math.Cohomology.CupAW.Leibniz21Bridge
