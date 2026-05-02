import E213.Math.Cohomology.CupAW.Core
import E213.Math.Cohomology.Universal.Prop51

/-!
# Cup Leibniz universal at (5, 1, 1) — AW cup version

Test if Alexander–Whitney cup with overlap satisfies Leibniz
universally at the (5, 1, 1) Δ⁴ vertex case, where the original
cup failed (per LeibnizFinding).

  ∀ α β : Cochain 5 1,
    δ(α ⌣AW β) = δα ⌣AW β  XOR  α ⌣AW δβ
  in Cochain 5 2.

Pattern enumeration: 32 × 32 = 1024 (α, β) pairs × 10 indices.
-/

namespace E213.Math.Cohomology.CupAW.Leibniz

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Universal.Prop51 (pattern)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.Core (cupAW)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Math.Cohomology.Cup.Core (cup)

set_option maxHeartbeats 16000000 in
/-- Leibniz on every pattern pair — decide-checked. -/
theorem leibniz_pattern_5_1_1 :
    ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 2),
        delta (cupAW 5 1 1 (pattern a0 a1 a2 a3 a4)
                              (pattern b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 1 (delta (pattern a0 a1 a2 a3 a4))
                              (pattern b0 b1 b2 b3 b4) i)
                (cupAW 5 1 2 (pattern a0 a1 a2 a3 a4)
                              (delta (pattern b0 b1 b2 b3 b4)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (5, 1, 1) — AW cup. -/
theorem leibniz_universal_5_1_1
    (α β : Cochain 5 1) (i : Fin (binom 5 2)) :
    delta (cupAW 5 1 1 α β) i
      = xor (cupAW 5 2 1 (delta α) β i)
            (cupAW 5 1 2 α (delta β) i) := by
  rw [E213.Math.Cohomology.Universal.Prop51.pattern_eq α, E213.Math.Cohomology.Universal.Prop51.pattern_eq β]
  exact leibniz_pattern_5_1_1 _ _ _ _ _ _ _ _ _ _ i

end E213.Math.Cohomology.CupAW.Leibniz
