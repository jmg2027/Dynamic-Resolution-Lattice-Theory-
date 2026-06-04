import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogSeries
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogODE
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogExpInverse

/-!
# Real213 — `cutLog` Capstone synthesis

4 cluster witnesses + total bundle.  All ∅-axiom.

The `Real213.cutLog` Taylor layer mirrors `Real213.CutExpSeries.cutExp`:
both are positive partial-sum towers truncated at finite Grade-N,
without Cauchy-modulus chase.  Together they close the long-deferred
"`Real213.log` is not built" item from PRs #38 / Probability INDEX.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogCapstone

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogSeries
  (cutLog logPartialSum logTermAt logPartialSum_zero cutLog_zero
   logPartialSum_succ logTermAt_zero)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogODE
  (geomTermAt geomPartialSum geomPartialSum_zero geomPartialSum_one
   cutLog_derivative_skeleton)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogExpInverse
  (exp_log_zero_baseline exp_of_log_zero log_of_exp_zero
   inverse_baseline_at_zero)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- ★ **Series witness** — partial-sum recursion + first term. -/
theorem series_witness (x : Nat → Nat → Bool) (N : Nat) :
    logPartialSum x 0 = constCut 0 1
    ∧ cutLog x 0 = constCut 0 1
    ∧ logPartialSum x (N + 1)
        = E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum
            (logPartialSum x N) (logTermAt x N) :=
  ⟨logPartialSum_zero x, cutLog_zero x, logPartialSum_succ x N⟩

/-- ★ **ODE witness** — geometric partial-sum bridge. -/
theorem ode_witness (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x 0 = constCut 0 1
    ∧ geomPartialSum x N
        = E213.Lib.Math.Analysis.Series.CutSeries.partialSum
            (geomTermAt x) N :=
  ⟨geomPartialSum_zero x, cutLog_derivative_skeleton x N⟩

/-- ★ **Inverse witness** — `cutExp ∘ cutLog` and converse at the
    depth-0 baseline. -/
theorem inverse_witness (x : Nat → Nat → Bool) :
    E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp x 0 = constCut 0 1
    ∧ cutLog x 0 = constCut 0 1
    ∧ E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp (cutLog x 0) 0
        = constCut 0 1
    ∧ cutLog (E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp x 0) 0
        = constCut 0 1 :=
  ⟨(exp_log_zero_baseline x).1, (exp_log_zero_baseline x).2,
   exp_of_log_zero x, log_of_exp_zero x⟩

/-- ★★★ **Total witness** ★★★ — series, ODE, inverse all bundled. -/
theorem total_witness (x : Nat → Nat → Bool) (N : Nat) :
    cutLog x 0 = constCut 0 1
    ∧ logPartialSum x (N + 1)
        = E213.Lib.Math.NumberSystems.Real213.Sum.CutSum.cutSum
            (logPartialSum x N) (logTermAt x N)
    ∧ geomPartialSum x 0 = constCut 0 1
    ∧ E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries.cutExp (cutLog x 0) 0
        = constCut 0 1 :=
  ⟨cutLog_zero x, logPartialSum_succ x N, geomPartialSum_zero x,
   exp_of_log_zero x⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogCapstone
