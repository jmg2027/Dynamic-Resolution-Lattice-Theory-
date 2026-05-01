import E213.Math.Cohomology.CupAWBilinearFunc
import E213.Math.Cohomology.CupAWZero
import E213.Math.Cohomology.CupAWBasisLeibniz
import E213.Math.Cohomology.Cochain5_1DecompR
import E213.Math.Cohomology.Cochain5_2Decomp
import E213.Math.Cohomology.XorPairCombine

/-!
# Algebraic Leibniz lift at (5, 2, 1) — β-side lens

α : Cochain 5 2, β : Cochain 5 1.  Decompose β (5 components),
reduce to per-component (∀ α, basis_k) Leibniz, close residual
via `combine_5`.
-/

namespace E213.Math.Cohomology.CupAWLeibnizAlgLift21

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.Cochain5_1DecompR (decomp_5_1 decomp_5_1_eq bz5_1)
open E213.Math.XorPairCombine (combine_5)

/-- ★ β-decomp lens at (5, 2, 1). -/
theorem leibniz_via_β_decomp_21
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3))
    (h_components : ∀ k : Fin 5,
      delta (cupAW 5 2 1 α (bz5_1 β k)) i
        = xor (cupAW 5 3 1 (delta α) (bz5_1 β k) i)
              (cupAW 5 2 2 α (delta (bz5_1 β k)) i)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) := by
  rw [← decomp_5_1_eq β]
  unfold decomp_5_1
  simp only [cupAW_add_right_eq, delta_add_eq,
             cupAW_add_right, delta_add, h_components]
  exact combine_5
    (cupAW 5 3 1 (delta α) (bz5_1 β ⟨0, by decide⟩) i)
    (cupAW 5 3 1 (delta α) (bz5_1 β ⟨1, by decide⟩) i)
    (cupAW 5 3 1 (delta α) (bz5_1 β ⟨2, by decide⟩) i)
    (cupAW 5 3 1 (delta α) (bz5_1 β ⟨3, by decide⟩) i)
    (cupAW 5 3 1 (delta α) (bz5_1 β ⟨4, by decide⟩) i)
    (cupAW 5 2 2 α (delta (bz5_1 β ⟨0, by decide⟩)) i)
    (cupAW 5 2 2 α (delta (bz5_1 β ⟨1, by decide⟩)) i)
    (cupAW 5 2 2 α (delta (bz5_1 β ⟨2, by decide⟩)) i)
    (cupAW 5 2 2 α (delta (bz5_1 β ⟨3, by decide⟩)) i)
    (cupAW 5 2 2 α (delta (bz5_1 β ⟨4, by decide⟩)) i)

end E213.Math.Cohomology.CupAWLeibnizAlgLift21
