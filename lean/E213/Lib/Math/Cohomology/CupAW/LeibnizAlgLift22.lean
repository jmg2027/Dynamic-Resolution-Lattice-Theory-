import E213.Lib.Math.Cohomology.CupAW.BilinearFunc
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.XorPairCombine
import E213.Term.Tactic.Nat213

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Algebraic Leibniz lift at (5, 2, 2) — β-side and α-side lenses

Same bilinearity-lens technique as (5, 1, 2), specialised for
α : Cochain 5 2, β : Cochain 5 2.

Two lenses:
  - β-decomp: reduces (∀ α β) to per-component (∀ α, basis_q)
  - α-decomp (with β = basis q): reduces to per-component
    (basis_p, basis_q) — closed by `basis_leibniz_5_2_2`
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (decomp_5_2 decomp_5_2_eq bz5_2)
open E213.Lib.Math.Cohomology.XorPairCombine (combine_10)
open E213.Lib.Math.Cohomology.CupAW.BilinearFunc (cupAW_add_right_eq cupAW_add_left_eq delta_add_eq)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left cupAW_add_right)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
  (decomp_step_at_0 decomp_step_at_1 decomp_step_at_2 decomp_step_at_3
   decomp_step_at_4 decomp_step_at_5 decomp_step_at_6 decomp_step_at_7
   decomp_step_at_8 decomp_step_at_9)
open E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
  (delta_cupAW_add_right cupAW_delta_add_right)
open E213.Tactic.Nat213 (cases_lt_ten)

/-- ★ β-decomp lens at (5, 2, 2). -/
theorem leibniz_via_β_decomp_22
    (α β : Cochain 5 2) (i : Fin (binom 5 4))
    (h_components : ∀ q : Fin 10,
      delta (cupAW 5 2 2 α (bz5_2 β q)) i
        = xor (cupAW 5 3 2 (delta α) (bz5_2 β q) i)
              (cupAW 5 2 3 α (delta (bz5_2 β q)) i)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) := by
  -- PURE: pointwise lifts via per-index decomp_step_at_* + value-level
  -- bilinearity from PointwiseBilinear.  Avoids decomp_5_2_eq funext leak.
  have h_β_pw : ∀ j, β j = decomp_5_2 β j := by
    intro j; rcases j with ⟨n, hn⟩
    rcases (cases_lt_ten hn) with rfl | rfl | rfl | rfl | rfl | rfl
                                | rfl | rfl | rfl | rfl
    · exact (decomp_step_at_0 β).symm
    · exact (decomp_step_at_1 β).symm
    · exact (decomp_step_at_2 β).symm
    · exact (decomp_step_at_3 β).symm
    · exact (decomp_step_at_4 β).symm
    · exact (decomp_step_at_5 β).symm
    · exact (decomp_step_at_6 β).symm
    · exact (decomp_step_at_7 β).symm
    · exact (decomp_step_at_8 β).symm
    · exact (decomp_step_at_9 β).symm
  have h_lhs : delta (cupAW 5 2 2 α β) i
             = delta (cupAW 5 2 2 α (decomp_5_2 β)) i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq α α β (decomp_5_2 β) (fun _ => rfl) h_β_pw j
  have h_rhs1 : cupAW 5 3 2 (delta α) β i
              = cupAW 5 3 2 (delta α) (decomp_5_2 β) i :=
    cupAW_pointwise_eq (delta α) (delta α) β (decomp_5_2 β)
      (fun _ => rfl) h_β_pw i
  have h_delta_β_pw : ∀ j, delta β j = delta (decomp_5_2 β) j :=
    fun j => delta_pointwise_eq β (decomp_5_2 β) h_β_pw j
  have h_rhs2 : cupAW 5 2 3 α (delta β) i
              = cupAW 5 2 3 α (delta (decomp_5_2 β)) i :=
    cupAW_pointwise_eq α α (delta β) (delta (decomp_5_2 β))
      (fun _ => rfl) h_delta_β_pw i
  rw [h_lhs, h_rhs1, h_rhs2]
  unfold decomp_5_2
  rw [delta_cupAW_add_right, delta_cupAW_add_right, delta_cupAW_add_right,
      delta_cupAW_add_right, delta_cupAW_add_right, delta_cupAW_add_right,
      delta_cupAW_add_right, delta_cupAW_add_right, delta_cupAW_add_right,
      cupAW_add_right, cupAW_add_right, cupAW_add_right,
      cupAW_add_right, cupAW_add_right, cupAW_add_right,
      cupAW_add_right, cupAW_add_right, cupAW_add_right,
      cupAW_delta_add_right, cupAW_delta_add_right, cupAW_delta_add_right,
      cupAW_delta_add_right, cupAW_delta_add_right, cupAW_delta_add_right,
      cupAW_delta_add_right, cupAW_delta_add_right, cupAW_delta_add_right,
      h_components ⟨0, by decide⟩, h_components ⟨1, by decide⟩,
      h_components ⟨2, by decide⟩, h_components ⟨3, by decide⟩,
      h_components ⟨4, by decide⟩, h_components ⟨5, by decide⟩,
      h_components ⟨6, by decide⟩, h_components ⟨7, by decide⟩,
      h_components ⟨8, by decide⟩, h_components ⟨9, by decide⟩]
  exact combine_10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22
