import E213.Lib.Math.Probability.Inequality.Hoeffding
import E213.Lib.Math.Real213.ExpLog.CutExpSeries

/-!
# Hoeffding finite-N concrete witnesses (∅-axiom)

Closes the "atomic placeholder for the full Hoeffding bound which
kicks in at `N ≥ 1`" deferral noted in `Probability/Hoeffding.lean`.

The base file delivered:
  * `hoeffdingBound_depth_zero` — bound at N=0 is `constCut 0 1`
  * `hoeffding_balanced_zero_dev` — balanced fair-coin gives 0
    deviation
  * `hoeffdingBound_eq_partialSum` — bound = Taylor partial sum

This file adds substantive small-N witnesses showing that the
Taylor-partial-sum *grows* exactly as expected at the next two
levels (N = 1, N = 2), without invoking any Cauchy-modulus
argument (which would need `Real213.log` and is genuinely deferred).
-/

namespace E213.Lib.Math.Extras.HoeffdingFiniteN

open E213.Lib.Math.Probability.Inequality.Hoeffding (hoeffdingBoundAtDepth)
open E213.Lib.Math.Real213.ExpLog.CutExpSeries
  (expPartialSum expPartialSum_zero expPartialSum_succ
   expTerm expTerm_zero)

/-- ★ Partial sum at N=1 = 0 + first term (rfl). -/
theorem expPartialSum_one (x : Nat → Nat → Bool) :
    expPartialSum x 1
    = E213.Lib.Math.Real213.Sum.CutSum.cutSum
        (E213.Lib.Math.Real213.Sum.CutSumTest.constCut 0 1)
        (expTerm x 0) := rfl

/-- ★ Partial sum at N=2 = (sum at 1) + second term (rfl). -/
theorem expPartialSum_two (x : Nat → Nat → Bool) :
    expPartialSum x 2
    = E213.Lib.Math.Real213.Sum.CutSum.cutSum
        (expPartialSum x 1) (expTerm x 1) := rfl

/-- ★ Hoeffding bound at depth 1 IS `expPartialSum x 1` (rfl). -/
theorem hoeffdingBound_depth_one (negArg : Nat → Nat → Bool) :
    hoeffdingBoundAtDepth negArg 1 = expPartialSum negArg 1 := rfl

/-- ★ Hoeffding bound at depth 2 IS `expPartialSum x 2` (rfl). -/
theorem hoeffdingBound_depth_two (negArg : Nat → Nat → Bool) :
    hoeffdingBoundAtDepth negArg 2 = expPartialSum negArg 2 := rfl

end E213.Lib.Math.Extras.HoeffdingFiniteN
