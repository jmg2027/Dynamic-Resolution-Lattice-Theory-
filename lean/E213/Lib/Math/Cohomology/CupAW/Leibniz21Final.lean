import E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
import E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# (5, 2, 1) Universal Cup AW Leibniz — closed via two-lens lift
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz21Final

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis basis_leibniz_5_2_1)
open E213.Lib.Math.Cohomology.Cochain.V5_1DecompR (bz5_1)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge (bz5_2_false_at bz5_2_true_at)
open E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge (bz5_1_false_at bz5_1_true_at)
open E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp
  (leibniz_zero_collapse_left_5_2_1 leibniz_pointwise_transport_left_5_2_1
   leibniz_zero_collapse_right_5_2_1 leibniz_pointwise_transport_right_5_2_1)

/-- Per-α-component Leibniz at (bz5_2 α p, basis 5 1 k).  PURE.
    Reduced to LeibnizDecomp helpers ( L2). -/
theorem h_components_α (α : Cochain 5 2) (k : Fin 5)
    (i : Fin (binom 5 3)) (p : Fin 10) :
    delta (cupAW 5 2 1 (bz5_2 α p) (basis 5 1 k)) i
      = xor (cupAW 5 3 1 (delta (bz5_2 α p)) (basis 5 1 k) i)
            (cupAW 5 2 2 (bz5_2 α p) (delta (basis 5 1 k)) i) := by
  cases hα : α p
  · exact leibniz_zero_collapse_left_5_2_1
      (bz5_2 α p) (basis 5 1 k) i (bz5_2_false_at α p hα)
  · exact leibniz_pointwise_transport_left_5_2_1
      (bz5_2 α p) (basis 5 2 p) (basis 5 1 k) i (bz5_2_true_at α p hα)
      (basis_leibniz_5_2_1 p k i)

/-- ∀ α : Cochain 5 2, Leibniz with β = basis 5 1 k. -/
theorem leibniz_α_basis (α : Cochain 5 2) (k : Fin 5)
    (i : Fin (binom 5 3)) :
    delta (cupAW 5 2 1 α (basis 5 1 k)) i
      = xor (cupAW 5 3 1 (delta α) (basis 5 1 k) i)
            (cupAW 5 2 2 α (delta (basis 5 1 k)) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21
    α (basis 5 1 k) i (h_components_α α k i)

/-- Per-β-component Leibniz: cases on β k.  PURE.
    Reduced to LeibnizDecomp helpers ( L2). -/
theorem h_components_β (α : Cochain 5 2) (β : Cochain 5 1)
    (i : Fin (binom 5 3)) (k : Fin 5) :
    delta (cupAW 5 2 1 α (bz5_1 β k)) i
      = xor (cupAW 5 3 1 (delta α) (bz5_1 β k) i)
            (cupAW 5 2 2 α (delta (bz5_1 β k)) i) := by
  cases hβ : β k
  · exact leibniz_zero_collapse_right_5_2_1
      α (bz5_1 β k) i (bz5_1_false_at β k hβ)
  · exact leibniz_pointwise_transport_right_5_2_1
      α (bz5_1 β k) (basis 5 1 k) i (bz5_1_true_at β k hβ)
      (leibniz_α_basis α k i)

/-- ★★★★★ Universal (5,2,1) Cup AW Leibniz — algebraic lift CLOSED. -/
theorem leibniz_universal_5_2_1
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21.leibniz_via_β_decomp_21
    α β i (h_components_β α β i)

end E213.Lib.Math.Cohomology.CupAW.Leibniz21Final
