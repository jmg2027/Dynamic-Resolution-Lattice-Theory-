import E213.Math.Cohomology.CupAW.Leibniz
import E213.Math.Cohomology.CupAW.Leibniz12Final
import E213.Math.Cohomology.CupAW.Leibniz21Final
import E213.Math.Cohomology.CupAW.Leibniz22Final

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

namespace E213.Math.Cohomology.Delta.V4LeibnizCapstone

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.Core (cupAW)
open E213.Math.Cohomology.Delta.Core (delta)

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
  ⟨E213.Math.Cohomology.CupAW.Leibniz.leibniz_universal_5_1_1,
   E213.Math.Cohomology.CupAW.Leibniz12Final.leibniz_universal_5_1_2,
   E213.Math.Cohomology.CupAW.Leibniz21Final.leibniz_universal_5_2_1,
   E213.Math.Cohomology.CupAW.Leibniz22Final.leibniz_universal_5_2_2⟩

end E213.Math.Cohomology.Delta.V4LeibnizCapstone
