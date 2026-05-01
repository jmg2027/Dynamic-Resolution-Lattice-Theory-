import E213.Math.Cohomology.CupAW.BilinearFunc
import E213.Math.Cohomology.CupAW.Zero
import E213.Math.Cohomology.CupAW.BasisLeibniz
import E213.Math.Cohomology.Cochain5_2Decomp
import E213.Math.Cohomology.XorPairCombine

/-!
# Algebraic Leibniz lift at (5, 2, 2) — β-side and α-side lenses

Same bilinearity-lens technique as (5, 1, 2), specialised for
α : Cochain 5 2, β : Cochain 5 2.

Two lenses:
  - β-decomp: reduces (∀ α β) to per-component (∀ α, basis_q)
  - α-decomp (with β = basis q): reduces to per-component
    (basis_p, basis_q) — closed by `basis_leibniz_5_2_2`
-/

namespace E213.Math.Cohomology.CupAW.LeibnizAlgLift22

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.Cochain5_2Decomp (decomp_5_2 decomp_5_2_eq bz5_2)
open E213.Math.XorPairCombine (combine_10)

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
  rw [← decomp_5_2_eq β]
  unfold decomp_5_2
  simp only [cupAW_add_right_eq, delta_add_eq,
             cupAW_add_right, delta_add, h_components]
  exact combine_10
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨0, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨1, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨2, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨3, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨4, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨5, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨6, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨7, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨8, by decide⟩) i)
    (cupAW 5 3 2 (delta α) (bz5_2 β ⟨9, by decide⟩) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨0, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨1, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨2, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨3, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨4, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨5, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨6, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨7, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨8, by decide⟩)) i)
    (cupAW 5 2 3 α (delta (bz5_2 β ⟨9, by decide⟩)) i)

end E213.Math.Cohomology.CupAW.LeibnizAlgLift22
