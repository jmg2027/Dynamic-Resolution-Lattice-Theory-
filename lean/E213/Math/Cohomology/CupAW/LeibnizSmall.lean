import E213.Math.Cohomology.CupAW.Core
import E213.Math.Cohomology.Universal.Prop31

import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.Cup.Core
import E213.Math.Cohomology.Delta.Core
import E213.Math.Cohomology.Hodge.Involution
import E213.Physics.Simplex.Counts
/-!
# Cup Leibniz at small atomic substrates — AW cup

  ∀ α β : Cochain n 1, δ(α ⌣AW β) = δα ⌣AW β XOR α ⌣AW δβ

For n = 3: 8 × 8 = 64 pairs × 3 indices = 192 evals.
Confirms the AW overlap convention is consistent with Leibniz
across multiple atomic substrates.
-/

namespace E213.Math.Cohomology.CupAW.LeibnizSmall

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.Core (cupAW)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Math.Cohomology.Universal.Prop31 (pattern)
open E213.Math.Cohomology.Cup.Core (cup)

/-- Leibniz on every (3, 1, 1) pattern pair. -/
theorem leibniz_pattern_3_1_1 :
    ∀ a0 a1 a2 b0 b1 b2 : Bool,
      ∀ i : Fin (binom 3 2),
        delta (cupAW 3 1 1 (pattern a0 a1 a2)
                            (pattern b0 b1 b2)) i
          = xor (cupAW 3 2 1 (delta (pattern a0 a1 a2))
                              (pattern b0 b1 b2) i)
                (cupAW 3 1 2 (pattern a0 a1 a2)
                              (delta (pattern b0 b1 b2)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (3, 1, 1) — AW cup. -/
theorem leibniz_universal_3_1_1
    (α β : Cochain 3 1) (i : Fin (binom 3 2)) :
    delta (cupAW 3 1 1 α β) i
      = xor (cupAW 3 2 1 (delta α) β i)
            (cupAW 3 1 2 α (delta β) i) := by
  rw [E213.Math.Cohomology.Universal.Prop31.pattern_eq α, E213.Math.Cohomology.Universal.Prop31.pattern_eq β]
  exact leibniz_pattern_3_1_1 _ _ _ _ _ _ i

end E213.Math.Cohomology.CupAW.LeibnizSmall
