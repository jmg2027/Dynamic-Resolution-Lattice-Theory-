import E213.Math.Cohomology.CupAWLeibnizAlgLift22

/-!
# Algebraic Leibniz lift at (5, 2, 2) — α-side lens

For β fixed (typically `basis 5 2 q`), decompose α : Cochain 5 2
into 10 basis components and apply bilinearity in α.
-/

namespace E213.Math.Cohomology.CupAWLeibnizAlgLift22Alpha

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.Cochain5_2Decomp (decomp_5_2 decomp_5_2_eq bz5_2)
open E213.Math.XorPairCombine (combine_10)

/-- ★ α-decomp lens at (5, 2, 2). -/
theorem leibniz_via_α_decomp_22
    (α β : Cochain 5 2) (i : Fin (binom 5 4))
    (h_components : ∀ p : Fin 10,
      delta (cupAW 5 2 2 (bz5_2 α p) β) i
        = xor (cupAW 5 3 2 (delta (bz5_2 α p)) β i)
              (cupAW 5 2 3 (bz5_2 α p) (delta β) i)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) := by
  rw [show α = decomp_5_2 α from (decomp_5_2_eq α).symm]
  unfold decomp_5_2
  simp only [cupAW_add_left_eq, delta_add_eq,
             cupAW_add_left, delta_add, h_components]
  exact combine_10
    (cupAW 5 3 2 (delta (bz5_2 α ⟨0, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨1, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨2, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨3, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨4, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨5, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨6, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨7, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨8, by decide⟩)) β i)
    (cupAW 5 3 2 (delta (bz5_2 α ⟨9, by decide⟩)) β i)
    (cupAW 5 2 3 (bz5_2 α ⟨0, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨1, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨2, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨3, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨4, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨5, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨6, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨7, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨8, by decide⟩) (delta β) i)
    (cupAW 5 2 3 (bz5_2 α ⟨9, by decide⟩) (delta β) i)

end E213.Math.Cohomology.CupAWLeibnizAlgLift22Alpha
