import E213.Math.Cohomology.CupAW
import E213.Math.Cohomology.UniversalProp41

/-!
# Cup Leibniz at (4, 1, 1) — AW cup, Δ³ tetrahedral

  ∀ α β : Cochain 4 1, δ(α ⌣AW β) = δα ⌣AW β XOR α ⌣AW δβ
  in Cochain 4 2.

Pattern: 16 × 16 = 256 pairs × 6 indices = 1536 evals.
-/

namespace E213.Math.Cohomology.CupAWLeibnizMid

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.UniversalProp41 (pattern)

/-- Leibniz on every (4, 1, 1) pattern pair. -/
theorem leibniz_pattern_4_1_1 :
    ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
      ∀ i : Fin (binom 4 2),
        delta (cupAW 4 1 1 (pattern a0 a1 a2 a3)
                            (pattern b0 b1 b2 b3)) i
          = xor (cupAW 4 2 1 (delta (pattern a0 a1 a2 a3))
                              (pattern b0 b1 b2 b3) i)
                (cupAW 4 1 2 (pattern a0 a1 a2 a3)
                              (delta (pattern b0 b1 b2 b3)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (4, 1, 1) — AW cup. -/
theorem leibniz_universal_4_1_1
    (α β : Cochain 4 1) (i : Fin (binom 4 2)) :
    delta (cupAW 4 1 1 α β) i
      = xor (cupAW 4 2 1 (delta α) β i)
            (cupAW 4 1 2 α (delta β) i) := by
  rw [UniversalProp41.pattern_eq α, UniversalProp41.pattern_eq β]
  exact leibniz_pattern_4_1_1 _ _ _ _ _ _ _ _ i

end E213.Math.Cohomology.CupAWLeibnizMid
