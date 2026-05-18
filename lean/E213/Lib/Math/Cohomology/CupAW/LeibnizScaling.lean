import E213.Lib.Math.Cohomology.CupAW.Leibniz
import E213.Lib.Math.Cohomology.CupAW.LeibnizSmall
import E213.Lib.Math.Cohomology.CupAW.LeibnizMid
import E213.Lib.Math.Cohomology.Examples.EncodingBijection52

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# AW Cup Leibniz — closed cases bundle

## Closed Prop-level Universal Leibniz (PURE; verified 2026-05-18)

  - (3, 1, 1) — `E213.Lib.Math.Cohomology.CupAW.LeibnizSmall.leibniz_universal_3_1_1`
  - (4, 1, 1) — `E213.Lib.Math.Cohomology.CupAW.LeibnizMid.leibniz_universal_4_1_1`
  - (5, 1, 1) — `E213.Lib.Math.Cohomology.CupAW.Leibniz.leibniz_universal_5_1_1`

## Honest scaling note at (5, 1, 2)

Cup Leibniz at (5, 1, 2) requires 32 × 1024 × 10 = 327,680 cases.
Both attempted strategies hit kernel-level resource limits in
Lean 4 core under the project's strict-axiom rule:

  * Prop-level `∀ a0..b9 : Bool, decide` builds one giant kernel
    proof term → 7+ GB RAM, OOM-killed.
  * Bool-level `List.all` enumeration via `cochainAt` fits in
    memory but exceeds `maxRecDepth` even at 4M; bumping further
    OOMs at kernel reduction time.

Encoding bijection at (5, 2) is now closed (`EncodingBijection52`)
and provides the bridge for any future Bool-level (5, 1, 2) result.
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizScaling

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)

/-- ★★★ AW Cup Leibniz universal Prop-lift — closed configurations
    (3, 1, 1), (4, 1, 1), (5, 1, 1).  Each PURE (∅-axiom; verified 2026-05-18). -/
theorem leibniz_aw_universal_closed_cases :
    (∀ α β : Cochain 3 1, ∀ i : Fin (binom 3 2),
       delta (cupAW 3 1 1 α β) i
         = xor (cupAW 3 2 1 (delta α) β i)
               (cupAW 3 1 2 α (delta β) i))
    ∧ (∀ α β : Cochain 4 1, ∀ i : Fin (binom 4 2),
         delta (cupAW 4 1 1 α β) i
           = xor (cupAW 4 2 1 (delta α) β i)
                 (cupAW 4 1 2 α (delta β) i))
    ∧ (∀ α β : Cochain 5 1, ∀ i : Fin (binom 5 2),
         delta (cupAW 5 1 1 α β) i
           = xor (cupAW 5 2 1 (delta α) β i)
                 (cupAW 5 1 2 α (delta β) i)) :=
  ⟨E213.Lib.Math.Cohomology.CupAW.LeibnizSmall.leibniz_universal_3_1_1,
   E213.Lib.Math.Cohomology.CupAW.LeibnizMid.leibniz_universal_4_1_1,
   E213.Lib.Math.Cohomology.CupAW.Leibniz.leibniz_universal_5_1_1⟩

end E213.Lib.Math.Cohomology.CupAW.LeibnizScaling
