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
# Algebraic Leibniz lift framework — bilinearity-driven

`leibniz_via_β_decomp_lens`: given basis-component Leibniz at α
with each `bz5_2 β k`, derives universal (5, 1, 2) Leibniz via
the bilinearity lens.  Reduction is purely algebraic — no
kernel-decide blow-up.

Pipeline inside the proof:
  - rw `← decomp_5_2_eq` : substitute β by 10-term explicit sum
  - simp `cupAW_add_right_eq, delta_add_eq, h_components` :
    expand bilinearity + linearity, apply per-component Leibniz
  - apply `combine_10` (structural XOR rearrangement, 0-axiom) :
    close the residual 20-Bool combinatorial identity
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (decomp_5_2)
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

/-- ★ Bilinearity-driven Leibniz reduction at (5, 1, 2). -/
theorem leibniz_via_β_decomp_lens
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3))
    (h_components : ∀ k : Fin 10,
      delta (cupAW 5 1 2 α
        (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β k)) i
        = xor (cupAW 5 2 2 (delta α)
                (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β k) i)
              (cupAW 5 1 3 α
                (delta (E213.Lib.Math.Cohomology.Cochain.V5_2Decomp.bz5_2 β k)) i)) :
    delta (cupAW 5 1 2 α β) i
      = xor (cupAW 5 2 2 (delta α) β i)
            (cupAW 5 1 3 α (delta β) i) := by
  -- PURE PATH: replace funext-based `rw [← decomp_5_2_eq β]` with
  -- pointwise lifts via per-index `decomp_step_at_*` (PURE) +
  -- cupAW/delta_pointwise_eq.  Then expand bilinearity with
  -- value-level helpers from PointwiseBilinear (PURE).
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
  have h_lhs : delta (cupAW 5 1 2 α β) i
             = delta (cupAW 5 1 2 α (decomp_5_2 β)) i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq α α β (decomp_5_2 β) (fun _ => rfl) h_β_pw j
  have h_rhs1 : cupAW 5 2 2 (delta α) β i
              = cupAW 5 2 2 (delta α) (decomp_5_2 β) i :=
    cupAW_pointwise_eq (delta α) (delta α) β (decomp_5_2 β)
      (fun _ => rfl) h_β_pw i
  have h_delta_β_pw : ∀ j, delta β j = delta (decomp_5_2 β) j :=
    fun j => delta_pointwise_eq β (decomp_5_2 β) h_β_pw j
  have h_rhs2 : cupAW 5 1 3 α (delta β) i
              = cupAW 5 1 3 α (delta (decomp_5_2 β)) i :=
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

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift
