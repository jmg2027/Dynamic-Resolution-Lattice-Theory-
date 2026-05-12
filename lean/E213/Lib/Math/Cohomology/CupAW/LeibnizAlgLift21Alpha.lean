import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Term.Tactic.Nat213

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.BilinearFunc
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Math.Cohomology.XorPairCombine
import E213.Lib.Physics.Simplex.Counts
/-!
# Algebraic Leibniz lift at (5, 2, 1) — α-side lens

For β fixed (typically `basis 5 1 k`), decompose α : Cochain 5 2
into 10 basis components and apply bilinearity in α.
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.CupAW.BilinearFunc (cupAW_add_right_eq cupAW_add_left_eq delta_add_eq)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left cupAW_add_right)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (decomp_5_2 decomp_5_2_eq bz5_2)
open E213.Lib.Math.Cohomology.XorPairCombine (combine_10)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
  (decomp_step_at_0 decomp_step_at_1 decomp_step_at_2 decomp_step_at_3
   decomp_step_at_4 decomp_step_at_5 decomp_step_at_6 decomp_step_at_7
   decomp_step_at_8 decomp_step_at_9)
open E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
  (delta_cupAW_add_left cupAW_delta_add_left)
open E213.Tactic.Nat213 (cases_lt_ten)

/-- ★ α-decomp lens at (5, 2, 1). -/
theorem leibniz_via_α_decomp_21
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3))
    (h_components : ∀ p : Fin 10,
      delta (cupAW 5 2 1 (bz5_2 α p) β) i
        = xor (cupAW 5 3 1 (delta (bz5_2 α p)) β i)
              (cupAW 5 2 2 (bz5_2 α p) (delta β) i)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) := by
  -- PURE: α-side decomp using delta_cupAW_add_left + cupAW_delta_add_left.
  have h_α_pw : ∀ j, α j = decomp_5_2 α j := by
    intro j; rcases j with ⟨n, hn⟩
    rcases (cases_lt_ten hn) with rfl | rfl | rfl | rfl | rfl | rfl
                                | rfl | rfl | rfl | rfl
    · exact (decomp_step_at_0 α).symm
    · exact (decomp_step_at_1 α).symm
    · exact (decomp_step_at_2 α).symm
    · exact (decomp_step_at_3 α).symm
    · exact (decomp_step_at_4 α).symm
    · exact (decomp_step_at_5 α).symm
    · exact (decomp_step_at_6 α).symm
    · exact (decomp_step_at_7 α).symm
    · exact (decomp_step_at_8 α).symm
    · exact (decomp_step_at_9 α).symm
  have h_lhs : delta (cupAW 5 2 1 α β) i
             = delta (cupAW 5 2 1 (decomp_5_2 α) β) i := by
    apply delta_pointwise_eq; intro j
    exact cupAW_pointwise_eq α (decomp_5_2 α) β β h_α_pw (fun _ => rfl) j
  have h_delta_α_pw : ∀ j, delta α j = delta (decomp_5_2 α) j :=
    fun j => delta_pointwise_eq α (decomp_5_2 α) h_α_pw j
  have h_rhs1 : cupAW 5 3 1 (delta α) β i
              = cupAW 5 3 1 (delta (decomp_5_2 α)) β i :=
    cupAW_pointwise_eq (delta α) (delta (decomp_5_2 α)) β β
      h_delta_α_pw (fun _ => rfl) i
  have h_rhs2 : cupAW 5 2 2 α (delta β) i
              = cupAW 5 2 2 (decomp_5_2 α) (delta β) i :=
    cupAW_pointwise_eq α (decomp_5_2 α) (delta β) (delta β)
      h_α_pw (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  unfold decomp_5_2
  rw [delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      h_components ⟨0, by decide⟩, h_components ⟨1, by decide⟩,
      h_components ⟨2, by decide⟩, h_components ⟨3, by decide⟩,
      h_components ⟨4, by decide⟩, h_components ⟨5, by decide⟩,
      h_components ⟨6, by decide⟩, h_components ⟨7, by decide⟩,
      h_components ⟨8, by decide⟩, h_components ⟨9, by decide⟩]
  exact combine_10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha
