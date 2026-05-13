import E213.Lib.Math.SignedCut.CD.CDTowerLevel
import E213.Lib.Math.NumberGrid.FSMGradeTaxonomy

/-!
# Dialogue Audit — Vertical (2-adic) vs Horizontal (5-adic) (∅-axiom)

The Gemini dialogue claimed:

> "둘은 방향만 다를 뿐 완벽하게 동일한 다이아딕(Dyadic) 분기
>  엔진으로 작동합니다."

**This is partially imprecise.**  Vertical and horizontal axes
saturate at the same index (25) but measure *different* base
quantities:

  * **Vertical (CD level)**: dimension `2^n` (2-adic doubling).
  * **Horizontal (FSM grade)**: states `5^n` (5-adic / d=5
    substrate).

Both saturate at n = 25 because the d=5 substrate's
distinguishability budget is `N_U = 5²⁵`, but the *units* are
different.

This file formalizes the distinction.
-/

namespace E213.Lib.Math.DialogueAudit.AxisDistinction

open E213.Lib.Math.SignedCut.CD.CDTowerLevel (levelDim)
open E213.Lib.Math.NumberGrid.FSMGradeTaxonomy (fsmGradeStates)

/-- ★ **Vertical at level 25** = 2²⁵ = 33,554,432. -/
theorem vertical_at_25 : levelDim 25 = 33554432 := rfl

/-- ★ **Horizontal at grade 25** = 5²⁵ = 298,023,223,876,953,125. -/
theorem horizontal_at_25 :
    fsmGradeStates 25 = 298023223876953125 := rfl

/-- ★ **The two ceilings are NOT equal**: vertical ≠ horizontal
    even at the same index 25. -/
theorem ceilings_unequal :
    levelDim 25 ≠ fsmGradeStates 25 := by decide

/-- ★ **Strict inequality**: horizontal ceiling > vertical
    ceiling at index 25.  Since `5 > 2`, `5²⁵ > 2²⁵`. -/
theorem horizontal_strictly_greater :
    levelDim 25 < fsmGradeStates 25 := by decide

/-- ★ **Vertical is 2-adic**: `levelDim (n+1) = 2 · levelDim n`. -/
theorem vertical_2adic (n : Nat) :
    levelDim (n + 1) = 2 * levelDim n := rfl

/-- ★ **Horizontal is 5-adic**: `fsmGradeStates (j+1)
    = fsmGradeStates j · 5`. -/
theorem horizontal_5adic (j : Nat) :
    fsmGradeStates (j + 1) = fsmGradeStates j * 5 := rfl

/-- ★ **Both saturate at index 25** (same index, different units). -/
theorem joint_index_saturation :
    levelDim 25 = 33554432
    ∧ fsmGradeStates 25 = 298023223876953125 :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.DialogueAudit.AxisDistinction
