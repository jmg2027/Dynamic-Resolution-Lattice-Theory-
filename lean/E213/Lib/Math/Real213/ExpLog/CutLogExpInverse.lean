import E213.Lib.Math.Real213.ExpLog.CutLogSeries
import E213.Lib.Math.Real213.ExpLog.CutExpSeries

/-!
# Real213 — `cutLog` ↔ `cutExp` formal inverse skeleton

In ZFC, `exp ∘ log = id` is an analytic-continuation identity.
In 213-native at finite Grade-N, the relationship is the
*formal-series compositional inverse* (modulo Grade-N
truncation residue).

This file provides the structural witnesses:
  * Both `cutExp x 0` and `cutLog x 0` equal `0` (the empty
    partial sum).  Bridge: trivial baseline.
  * `cutExp` of `cutLog x 0` = `cutExp (constCut 0 1) 0` = 0.
  * The full `exp ∘ log = id` identity at depth `N` is a
    polynomial identity modulo `x^(N+1)` — left as the next
    step (mirrors `Cohomology.CutLog.cutLog_cup_grade_6_zero`
    pattern).
-/

namespace E213.Lib.Math.Real213.ExpLog.CutLogExpInverse

open E213.Lib.Math.Real213.ExpLog.CutLogSeries (cutLog logPartialSum cutLog_zero)
open E213.Lib.Math.Real213.ExpLog.CutExpSeries (cutExp expPartialSum)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- ★ Both expansions zero out at depth 0 (rfl). -/
theorem exp_log_zero_baseline (x : Nat → Nat → Bool) :
    cutExp x 0 = constCut 0 1
    ∧ cutLog x 0 = constCut 0 1 :=
  ⟨rfl, cutLog_zero x⟩

/-- ★ Composition at depth-0 endpoint: `cutExp (cutLog x 0) 0
    = constCut 0 1`. -/
theorem exp_of_log_zero (x : Nat → Nat → Bool) :
    cutExp (cutLog x 0) 0 = constCut 0 1 := rfl

/-- ★ Composition at depth-0 endpoint (other direction):
    `cutLog (cutExp x 0) 0 = constCut 0 1`. -/
theorem log_of_exp_zero (x : Nat → Nat → Bool) :
    cutLog (cutExp x 0) 0 = constCut 0 1 := rfl

/-- ★ At `x = 0`, both `cutLog` and `cutExp` give pure baselines:
    `cutLog 0 0 = 0`, `cutExp 0 0 = 0`.  The full inverse
    `cutExp(cutLog x) = x` modulo Grade-N is left for the
    polynomial-ring inverse marathon. -/
theorem inverse_baseline_at_zero :
    cutLog (constCut 0 1) 0 = constCut 0 1
    ∧ cutExp (constCut 0 1) 0 = constCut 0 1 :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.Real213.ExpLog.CutLogExpInverse
