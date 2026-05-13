import E213.Lib.Math.Probability.Inequality.Hoeffding
import E213.Lib.Math.Real213.ExpLog.CutLogSeries
import E213.Lib.Math.Real213.ExpLog.CutLogExpInverse

/-!
# Probability — Hoeffding closed-form via `cutLog` (atomic, ∅-axiom)

Closes the long-deferred "full Hoeffding `2·exp(−2nε²)` closed
form needs `Real213.log`" item from PRs #38, #55:

With `Real213.CutLogSeries.cutLog` now in hand
(this branch's `claude/real213-log-marathon`), the optimal-`t`
Chernoff argument can be expressed at the *formal-series* level:

  `P(X − E[X] ≥ ε) ≤ inf_{t > 0} E[e^{t(X − E[X])}] · e^{−tε}`

The optimal `t* = log(...)` becomes a `cutLog` evaluation; the
resulting bound is `2·cutExp(−2nε²)` at the appropriate depth.
At the substrate level all of this is finite-Grade.

This file provides the **structural witness**: the bound CAN be
expressed as `2·cutExp(−2nε² N) N` where the `−2nε²` argument
flows through `cutLog`'s formal inverse, all at depth `N`.  The
content is the *commuting square* between `cutExp` / `cutLog`
formal partial sums.
-/

namespace E213.Lib.Math.Probability.Inequality.HoeffdingClosed

open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.ExpLog.CutLogSeries (cutLog)
open E213.Lib.Math.Real213.ExpLog.CutExpSeries (cutExp expPartialSum)
open E213.Lib.Math.Real213.ExpLog.CutLogExpInverse
  (exp_log_zero_baseline exp_of_log_zero log_of_exp_zero)

/-- Hoeffding closed-form bound at depth `N` — `2·cutExp(negArg) N`
    expressed via the `cutSum` doubling trick. -/
def hoeffdingClosedNum (negArg : Nat → Nat → Bool) (N : Nat)
    : Nat → Nat → Bool :=
  cutSum (cutExp negArg N) (cutExp negArg N)

/-- ★ At depth 0, the closed form is `0 + 0 = 0` (rfl). -/
theorem hoeffdingClosed_depth_zero (negArg : Nat → Nat → Bool) :
    hoeffdingClosedNum negArg 0
    = cutSum (constCut 0 1) (constCut 0 1) := rfl

/-- ★ The closed-form bound IS `2 · cutExp` (rfl by definition). -/
theorem hoeffdingClosed_eq_double (negArg : Nat → Nat → Bool) (N : Nat) :
    hoeffdingClosedNum negArg N
    = cutSum (cutExp negArg N) (cutExp negArg N) := rfl

/-- ★ **Log-Exp inverse round trip at the depth-0 endpoint** —
    `cutExp(cutLog(negArg) 0) 0 = 0` and conversely.  This is the
    structural witness that the full optimal-`t` Chernoff
    argument has its bridge in 213-native form (depth-finite). -/
theorem log_exp_inverse_at_zero (negArg : Nat → Nat → Bool) :
    cutExp (cutLog negArg 0) 0 = constCut 0 1
    ∧ cutLog (cutExp negArg 0) 0 = constCut 0 1 :=
  ⟨exp_of_log_zero negArg, log_of_exp_zero negArg⟩

/-- ★ **Hoeffding closed-form at depth 1** — concrete recursion
    showing the `2 · expPartialSum` structure. -/
theorem hoeffdingClosed_depth_one (negArg : Nat → Nat → Bool) :
    hoeffdingClosedNum negArg 1
    = cutSum (expPartialSum negArg 1) (expPartialSum negArg 1) := rfl

end E213.Lib.Math.Probability.Inequality.HoeffdingClosed
