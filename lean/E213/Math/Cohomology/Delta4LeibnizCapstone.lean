import E213.Math.Cohomology.CupAWLeibniz
import E213.Math.Cohomology.CupAWLeibniz12Final
import E213.Math.Cohomology.CupAWLeibniz21Final
import E213.Math.Cohomology.CupAWLeibniz22Final

/-!
# Δ⁴ Cup AW Leibniz — full coverage capstone

All four interior-stratum Leibniz instances on the Δ⁴ atomic
substrate (n = 5), closed under ≤ {propext, Quot.sound}:

  - (5, 1, 1) — vertex × vertex,    direct decide
  - (5, 1, 2) — vertex × edge,      bilinearity lens
  - (5, 2, 1) — edge   × vertex,    bilinearity lens (two-sided)
  - (5, 2, 2) — edge   × edge,      bilinearity lens (two-sided)

Together these constitute the complete first-order graded-Leibniz
structure on Δ⁴ for `cupAW` with the standard simplicial
Alexander–Whitney overlap convention.
-/

namespace E213.Math.Cohomology.Delta4LeibnizCapstone

open E213.Physics.Simplex (binom)

/-- ★★★★★ Δ⁴ full Cup AW Leibniz capstone — ∀ α β ∀ i. -/
theorem delta4_leibniz_capstone :
    (∀ α β : Cochain 5 1, ∀ i : Fin (binom 5 2),
       delta (cupAW 5 1 1 α β) i
         = xor (cupAW 5 2 1 (delta α) β i)
               (cupAW 5 1 2 α (delta β) i))
    ∧ (∀ α : Cochain 5 1, ∀ β : Cochain 5 2, ∀ i : Fin (binom 5 3),
         delta (cupAW 5 1 2 α β) i
           = xor (cupAW 5 2 2 (delta α) β i)
                 (cupAW 5 1 3 α (delta β) i))
    ∧ (∀ α : Cochain 5 2, ∀ β : Cochain 5 1, ∀ i : Fin (binom 5 3),
         delta (cupAW 5 2 1 α β) i
           = xor (cupAW 5 3 1 (delta α) β i)
                 (cupAW 5 2 2 α (delta β) i))
    ∧ (∀ α β : Cochain 5 2, ∀ i : Fin (binom 5 4),
         delta (cupAW 5 2 2 α β) i
           = xor (cupAW 5 3 2 (delta α) β i)
                 (cupAW 5 2 3 α (delta β) i)) :=
  ⟨CupAWLeibniz.leibniz_universal_5_1_1,
   CupAWLeibniz12Final.leibniz_universal_5_1_2,
   CupAWLeibniz21Final.leibniz_universal_5_2_1,
   CupAWLeibniz22Final.leibniz_universal_5_2_2⟩

end E213.Math.Cohomology.Delta4LeibnizCapstone
