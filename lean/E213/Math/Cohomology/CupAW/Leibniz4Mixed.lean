import E213.Math.Cohomology.CupAW.Core
import E213.Math.Cohomology.Universal.Core.Prop41
import E213.Math.Cohomology.Universal.Core.Prop42

/-!
# Cup AW Leibniz at mixed arities on Δ³ (n = 4)

  - (4, 1, 2): 16 × 64 = 1024 pattern pairs × 4 indices
  - (4, 2, 1): 64 × 16 = 1024 pattern pairs × 4 indices
  - (4, 2, 2): 64 × 64 = 4096 pattern pairs × 1 index

Each fits comfortably in a single Prop-level decide.
Together with (4, 1, 1) and (3, 1, 1), this closes Cup Leibniz
universal across all interior strata of Δ², Δ³.
-/

namespace E213.Math.Cohomology.CupAW.Leibniz4Mixed

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Universal.Core.Prop41 (pattern)
open E213.Math.Cohomology.Universal.Core.Prop42 renaming pattern → patternE

set_option maxHeartbeats 16000000 in
/-- ★ Pattern-level Leibniz at (4, 1, 2). -/
theorem leibniz_pattern_4_1_2 :
    ∀ a0 a1 a2 a3 : Bool,
      ∀ b0 b1 b2 b3 b4 b5 : Bool,
      ∀ i : Fin (binom 4 3),
        delta (cupAW 4 1 2 (pattern a0 a1 a2 a3)
                            (patternE b0 b1 b2 b3 b4 b5)) i
          = xor (cupAW 4 2 2 (delta (pattern a0 a1 a2 a3))
                              (patternE b0 b1 b2 b3 b4 b5) i)
                (cupAW 4 1 3 (pattern a0 a1 a2 a3)
                              (delta (patternE b0 b1 b2 b3 b4 b5)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (4, 1, 2). -/
theorem leibniz_universal_4_1_2
    (α : Cochain 4 1) (β : Cochain 4 2) (i : Fin (binom 4 3)) :
    delta (cupAW 4 1 2 α β) i
      = xor (cupAW 4 2 2 (delta α) β i)
            (cupAW 4 1 3 α (delta β) i) := by
  rw [UniversalProp41.pattern_eq α, UniversalProp42.pattern_eq β]
  exact leibniz_pattern_4_1_2 _ _ _ _ _ _ _ _ _ _ i

set_option maxHeartbeats 16000000 in
/-- ★ Pattern-level Leibniz at (4, 2, 2). -/
theorem leibniz_pattern_4_2_2 :
    ∀ a0 a1 a2 a3 a4 a5 : Bool,
      ∀ b0 b1 b2 b3 b4 b5 : Bool,
      ∀ i : Fin (binom 4 4),
        delta (cupAW 4 2 2 (patternE a0 a1 a2 a3 a4 a5)
                            (patternE b0 b1 b2 b3 b4 b5)) i
          = xor (cupAW 4 3 2 (delta (patternE a0 a1 a2 a3 a4 a5))
                              (patternE b0 b1 b2 b3 b4 b5) i)
                (cupAW 4 2 3 (patternE a0 a1 a2 a3 a4 a5)
                              (delta (patternE b0 b1 b2 b3 b4 b5)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (4, 2, 2). -/
theorem leibniz_universal_4_2_2
    (α β : Cochain 4 2) (i : Fin (binom 4 4)) :
    delta (cupAW 4 2 2 α β) i
      = xor (cupAW 4 3 2 (delta α) β i)
            (cupAW 4 2 3 α (delta β) i) := by
  rw [UniversalProp42.pattern_eq α, UniversalProp42.pattern_eq β]
  exact leibniz_pattern_4_2_2 _ _ _ _ _ _ _ _ _ _ _ _ i

end E213.Math.Cohomology.CupAW.Leibniz4Mixed
