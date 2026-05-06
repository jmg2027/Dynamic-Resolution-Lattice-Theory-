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

/-- bz5_1 with β k = false reduces to Cochain.zero. -/
theorem bz5_1_false (β : Cochain 5 1) (k : Fin 5)
    (hβ : β k = false) :
    bz5_1 β k = Cochain.zero 5 1 := by
  funext j
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- bz5_1 with β k = true reduces to basis 5 1 k. -/
theorem bz5_1_true (β : Cochain 5 1) (k : Fin 5)
    (hβ : β k = true) :
    bz5_1 β k = basis 5 1 k := by
  funext j
  show ((k.val == j.val) && β k) = basis 5 1 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

end E213.Lib.Math.Cohomology.CupAW.Leibniz21Bridge
