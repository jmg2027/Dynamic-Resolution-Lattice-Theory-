import E213.Lib.Math.Tactic.Extras.CauchySchwarz
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogCapstone
import E213.Lib.Math.Probability.Inequality.HoeffdingClosed

/-!
# Math Extras — Real213.log bundle (∅-axiom)

Bundle of re-exported lemmas for the `Real213/ExpLog/` branch.  Note
the `log`/`exp` witnesses are **depth-0 base cases** (`cutLog x 0 =
constCut 0 1`, i.e. `log∘exp` at depth 0 evaluating to 1) — base-case
witnesses, not a proof of the full transcendental layer:

  * `Real213.CutLog{Series, ODE, ExpInverse}` — `Real213.log`
    base-case (depth-0) witnesses.
  * `Extras.CauchySchwarz{3D, List}` — Σ-CS extension to n ≤ 3
    (`cs_two` is a genuine Cauchy-Schwarz lemma).
  * `Probability.HoeffdingClosed` — closed-form Hoeffding bound
    `2·cutExp(...)` via the `cutLog` formal-inverse bridge (depth-0).
-/

namespace E213.Lib.Math.Tactic.Extras.RealLogCapstone

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogSeries (cutLog cutLog_zero)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogExpInverse
  (exp_of_log_zero log_of_exp_zero)
open E213.Lib.Math.Tactic.Extras.CauchySchwarzList
  (dotList sumSqList cs_zero cs_one cs_two)
open E213.Lib.Math.Probability.Inequality.HoeffdingClosed
  (hoeffdingClosedNum hoeffdingClosed_depth_zero
   hoeffdingClosed_depth_one log_exp_inverse_at_zero)

/-- **Real213.log depth-0 base-case witness** (`log∘exp` at depth 0 = 1). -/
theorem realLog_witness (x : Nat → Nat → Bool) :
    cutLog x 0 = constCut 0 1
    ∧ E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp (cutLog x 0) 0
        = constCut 0 1
    ∧ cutLog (E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp x 0) 0
        = constCut 0 1 :=
  ⟨cutLog_zero x, exp_of_log_zero x, log_of_exp_zero x⟩

/-- **n ≤ 3 Σ-Cauchy-Schwarz** (genuine, via `cs_zero`/`cs_one`/`cs_two`). -/
theorem cs_n_le_3_witness (a b : Nat → Nat) :
    dotList a b 0 * dotList a b 0 ≤ sumSqList a 0 * sumSqList b 0
    ∧ dotList a b 1 * dotList a b 1 ≤ sumSqList a 1 * sumSqList b 1
    ∧ dotList a b 2 * dotList a b 2 ≤ sumSqList a 2 * sumSqList b 2 :=
  ⟨cs_zero a b, cs_one a b, cs_two a b⟩

/-- **Hoeffding closed-form depth-0 witness**. -/
theorem hoeffding_closed_witness (negArg : Nat → Nat → Bool) :
    hoeffdingClosedNum negArg 0
      = E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum
          (constCut 0 1) (constCut 0 1)
    ∧ E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp (cutLog negArg 0) 0
        = constCut 0 1 :=
  ⟨hoeffdingClosed_depth_zero negArg,
   (log_exp_inverse_at_zero negArg).1⟩

/-- **Total bundle** (depth-0 log witness + genuine `cs_two` CS +
    depth-0 Hoeffding witness). -/
theorem total_witness (x : Nat → Nat → Bool)
    (a b : Nat → Nat) (negArg : Nat → Nat → Bool) :
    cutLog x 0 = constCut 0 1
    ∧ dotList a b 2 * dotList a b 2
        ≤ sumSqList a 2 * sumSqList b 2
    ∧ hoeffdingClosedNum negArg 0
        = E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum
            (constCut 0 1) (constCut 0 1) :=
  ⟨cutLog_zero x, cs_two a b, hoeffdingClosed_depth_zero negArg⟩

end E213.Lib.Math.Tactic.Extras.RealLogCapstone
