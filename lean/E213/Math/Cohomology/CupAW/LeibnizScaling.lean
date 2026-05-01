import E213.Math.Cohomology.CupAW.Leibniz
import E213.Math.Cohomology.CupAW.LeibnizSmall
import E213.Math.Cohomology.CupAW.LeibnizMid
import E213.Math.Cohomology.EncodingBijection52

/-!
# AW Cup Leibniz — closed cases bundle

## Closed Prop-level Universal Leibniz (≤ {propext, Quot.sound})

  - (3, 1, 1) — `CupAWLeibnizSmall.leibniz_universal_3_1_1`
  - (4, 1, 1) — `CupAWLeibnizMid.leibniz_universal_4_1_1`
  - (5, 1, 1) — `CupAWLeibniz.leibniz_universal_5_1_1`

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

namespace E213.Math.Cohomology.CupAW.LeibnizScaling

open E213.Physics.Simplex.Counts (binom)

/-- ★★★ AW Cup Leibniz universal Prop-lift — closed configurations
    (3, 1, 1), (4, 1, 1), (5, 1, 1).  Each ≤ {propext, Quot.sound}. -/
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
  ⟨CupAWLeibnizSmall.leibniz_universal_3_1_1,
   CupAWLeibnizMid.leibniz_universal_4_1_1,
   CupAWLeibniz.leibniz_universal_5_1_1⟩

end E213.Math.Cohomology.CupAW.LeibnizScaling
