import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftAlpha
import E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
import E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# (5, 2, 2) Universal Cup AW Leibniz — closed via two-lens lift

α : Cochain 5 2, β : Cochain 5 2.  Lift via:
  1. Decompose β (10 components, basis or zero per `β q`)
  2. Per-(α, basis q) Leibniz: decompose α (10 components),
     reduces to (basis p, basis q) basis Leibniz
  3. Each `combine_10` closes the residual XOR rearrangement
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz22Final

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis basis_leibniz_5_2_2)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge (bz5_2_false_at bz5_2_true_at)
open E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp
  (leibniz_zero_collapse_left_5_2_2 leibniz_pointwise_transport_left_5_2_2
   leibniz_zero_collapse_right_5_2_2 leibniz_pointwise_transport_right_5_2_2)

/-- Per-α-component Leibniz at (bz5_2 α p, basis 5 2 q).  PURE.
    Reduced to LeibnizDecomp helpers ( L2). -/
theorem h_components_α (α : Cochain 5 2) (q : Fin 10)
    (i : Fin (binom 5 4)) (p : Fin 10) :
    delta (cupAW 5 2 2 (bz5_2 α p) (basis 5 2 q)) i
      = xor (cupAW 5 3 2 (delta (bz5_2 α p)) (basis 5 2 q) i)
            (cupAW 5 2 3 (bz5_2 α p) (delta (basis 5 2 q)) i) := by
  cases hα : α p
  · exact leibniz_zero_collapse_left_5_2_2
      (bz5_2 α p) (basis 5 2 q) i (bz5_2_false_at α p hα)
  · exact leibniz_pointwise_transport_left_5_2_2
      (bz5_2 α p) (basis 5 2 p) (basis 5 2 q) i (bz5_2_true_at α p hα)
      (basis_leibniz_5_2_2 p q i)

/-- ∀ α : Cochain 5 2, Leibniz with β = basis 5 2 q. -/
theorem leibniz_α_basis (α : Cochain 5 2) (q : Fin 10)
    (i : Fin (binom 5 4)) :
    delta (cupAW 5 2 2 α (basis 5 2 q)) i
      = xor (cupAW 5 3 2 (delta α) (basis 5 2 q) i)
            (cupAW 5 2 3 α (delta (basis 5 2 q)) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftAlpha.leibniz_via_α_decomp_22
    α (basis 5 2 q) i (h_components_α α q i)

/-- Per-β-component Leibniz: cases on β q.  PURE.
    Reduced to LeibnizDecomp helpers ( L2). -/
theorem h_components_β (α β : Cochain 5 2)
    (i : Fin (binom 5 4)) (q : Fin 10) :
    delta (cupAW 5 2 2 α (bz5_2 β q)) i
      = xor (cupAW 5 3 2 (delta α) (bz5_2 β q) i)
            (cupAW 5 2 3 α (delta (bz5_2 β q)) i) := by
  cases hβ : β q
  · exact leibniz_zero_collapse_right_5_2_2
      α (bz5_2 β q) i (bz5_2_false_at β q hβ)
  · exact leibniz_pointwise_transport_right_5_2_2
      α (bz5_2 β q) (basis 5 2 q) i (bz5_2_true_at β q hβ)
      (leibniz_α_basis α q i)

/-- ★★★★★ Universal Cup AW Leibniz at (5, 2, 2) — algebraic lift CLOSED. -/
theorem leibniz_universal_5_2_2
    (α β : Cochain 5 2) (i : Fin (binom 5 4)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22.leibniz_via_β_decomp_22
    α β i (h_components_β α β i)

end E213.Lib.Math.Cohomology.CupAW.Leibniz22Final
