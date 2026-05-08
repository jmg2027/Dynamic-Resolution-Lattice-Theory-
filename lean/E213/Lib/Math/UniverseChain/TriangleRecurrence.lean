import E213.Lib.Math.GenerationRule.TriangleIteration
import E213.Lib.Math.UniverseChain.PairAxes

/-!
# Step 3.5 — Triangle recurrence bridge (∅-axiom)

Mingu's chain step:
> "관계도 또 다른 관계 ⇒ 2+1 규칙 (둘 + 짝)
>  ⇒ a_{n+1} = a_n + C(a_n, 2)"

This file bridges G46's existing `triIter 2 n` sequence
(2, 3, 6, 21, 231, …) to the chain's named pair `(NT, NS)`
from `PairAxes`.

## Honest scope

Proven: the first two terms `triIter 2 0 = 2` and `triIter 2 1 = 3`
agree with `(NT, NS) = (2, 3)`.

Not proven (would require *uniqueness* over generation rules):
the triangle iteration *forces* the (2, 3) atomicity.  Many
generation rules pass through (2, 3); T is one of them, not the
unique one.  This is the strict reading of Step 3.5.
-/

namespace E213.Lib.Math.UniverseChain.TriangleRecurrence

open E213.Lib.Math.GenerationRule.TriangleIteration
  (T triIter triIter_2_0 triIter_2_1 triIter_2_2 triIter_2_3
   triIter_2_4 T_two T_three T_six T_twentyone)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- ★ **Step 3.5 pair**: `triIter 2 0 = NT, triIter 2 1 = NS`. -/
theorem step3_5_pair : triIter 2 0 = NT ∧ triIter 2 1 = NS :=
  ⟨rfl, rfl⟩

/-- ★ Atomicity-match: first two terms sum to 5 = d. -/
theorem atomicity_match :
    triIter 2 0 = NT
    ∧ triIter 2 1 = NS
    ∧ triIter 2 0 + triIter 2 1 = 5 :=
  ⟨rfl, rfl, rfl⟩

/-- ★ First five terms: 2, 3, 6, 21, 231. -/
theorem step3_5_first_terms :
    triIter 2 0 = 2
    ∧ triIter 2 1 = 3
    ∧ triIter 2 2 = 6
    ∧ triIter 2 3 = 21
    ∧ triIter 2 4 = 231 :=
  ⟨triIter_2_0, triIter_2_1, triIter_2_2, triIter_2_3, triIter_2_4⟩

/-- ★ T(2) = 3 — the first non-trivial step. -/
theorem T_first_step : T 2 = 3 := T_two

/-- ★★★ **Step 3.5 capstone**: triangle recurrence agrees with
    `(NT, NS)` at the first two terms. -/
theorem step3_5_bundle :
    triIter 2 0 = NT
    ∧ triIter 2 1 = NS
    ∧ NT + NS = 5
    ∧ T 2 = 3 :=
  ⟨rfl, rfl, rfl, T_two⟩

end E213.Lib.Math.UniverseChain.TriangleRecurrence
