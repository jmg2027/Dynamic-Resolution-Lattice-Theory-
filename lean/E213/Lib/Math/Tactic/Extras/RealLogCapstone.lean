import E213.Lib.Math.Tactic.Extras.CauchySchwarz
import E213.Lib.Math.Real213.ExpLog.CutLogCapstone
import E213.Lib.Math.Probability.Inequality.HoeffdingClosed

/-!
# Math Extras — Real213.log marathon Capstone (∅-axiom)

3 cluster witnesses + total bundle for the
`Real213/ExpLog/` branch:

  * `Real213.CutLog{Series, ODE, ExpInverse}` — long-deferred
    `Real213.log` transcendental layer.
  * `Extras.CauchySchwarz{3D, List}` — Σ-CS extension to n ≤ 3.
  * `Probability.HoeffdingClosed` — closed-form Hoeffding bound
    `2·cutExp(...)` via the `cutLog` formal-inverse bridge.
-/

namespace E213.Lib.Math.Tactic.Extras.RealLogCapstone

open E213.Lib.Math.Real213.ExpLog.CutLogSeries (cutLog cutLog_zero)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.ExpLog.CutLogExpInverse
  (exp_of_log_zero log_of_exp_zero)
open E213.Lib.Math.Tactic.Extras.CauchySchwarzList
  (dotList sumSqList cs_zero cs_one cs_two)
open E213.Lib.Math.Probability.Inequality.HoeffdingClosed
  (hoeffdingClosedNum hoeffdingClosed_depth_zero
   hoeffdingClosed_depth_one log_exp_inverse_at_zero)

/-- ★ **Real213.log witness**. -/
theorem realLog_witness (x : Nat → Nat → Bool) :
    cutLog x 0 = constCut 0 1
    ∧ E213.Lib.Math.Real213.ExpLog.CutExpSeries.cutExp (cutLog x 0) 0
        = constCut 0 1
    ∧ cutLog (E213.Lib.Math.Real213.ExpLog.CutExpSeries.cutExp x 0) 0
        = constCut 0 1 :=
  ⟨cutLog_zero x, exp_of_log_zero x, log_of_exp_zero x⟩

/-- ★ **n ≤ 3 Σ-Cauchy-Schwarz witness**. -/
theorem cs_n_le_3_witness (a b : Nat → Nat) :
    dotList a b 0 * dotList a b 0 ≤ sumSqList a 0 * sumSqList b 0
    ∧ dotList a b 1 * dotList a b 1 ≤ sumSqList a 1 * sumSqList b 1
    ∧ dotList a b 2 * dotList a b 2 ≤ sumSqList a 2 * sumSqList b 2 :=
  ⟨cs_zero a b, cs_one a b, cs_two a b⟩

/-- ★ **Hoeffding closed-form witness**. -/
theorem hoeffding_closed_witness (negArg : Nat → Nat → Bool) :
    hoeffdingClosedNum negArg 0
      = E213.Lib.Math.Real213.Sum.CutSum.cutSum
          (constCut 0 1) (constCut 0 1)
    ∧ E213.Lib.Math.Real213.ExpLog.CutExpSeries.cutExp (cutLog negArg 0) 0
        = constCut 0 1 :=
  ⟨hoeffdingClosed_depth_zero negArg,
   (log_exp_inverse_at_zero negArg).1⟩

/-- ★★★ **Total witness** ★★★. -/
theorem total_witness (x : Nat → Nat → Bool)
    (a b : Nat → Nat) (negArg : Nat → Nat → Bool) :
    cutLog x 0 = constCut 0 1
    ∧ dotList a b 2 * dotList a b 2
        ≤ sumSqList a 2 * sumSqList b 2
    ∧ hoeffdingClosedNum negArg 0
        = E213.Lib.Math.Real213.Sum.CutSum.cutSum
            (constCut 0 1) (constCut 0 1) :=
  ⟨cutLog_zero x, cs_two a b, hoeffdingClosed_depth_zero negArg⟩

end E213.Lib.Math.Tactic.Extras.RealLogCapstone
