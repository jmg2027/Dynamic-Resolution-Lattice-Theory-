import E213.Lib.Math.Tactic.Extras.CauchySchwarz
import E213.Lib.Math.Tactic.Extras.HoeffdingFiniteN

/-!
# Math Extras — Aggregator Capstone (∅-axiom)

3 cluster witnesses + total bundle for the third cleanup pass:
  * n=2 Cauchy-Schwarz Σ-side aggregator
  * Hoeffding finite-N concrete witnesses (N = 1, 2)
-/

namespace E213.Lib.Math.Tactic.Extras.AggregatorCapstone

open E213.Lib.Math.Tactic.Extras.CauchySchwarz2D (cs_2d_le cross_term_le)
open E213.Lib.Math.Tactic.Extras.HoeffdingFiniteN
  (expPartialSum_one expPartialSum_two
   hoeffdingBound_depth_one hoeffdingBound_depth_two)

/-- ★ **n=2 Cauchy-Schwarz witness**. -/
theorem cs_2d_witness (a1 a2 b1 b2 : Nat) :
    (a1 * b1 + a2 * b2) * (a1 * b1 + a2 * b2)
      ≤ (a1 * a1 + a2 * a2) * (b1 * b1 + b2 * b2) :=
  cs_2d_le a1 a2 b1 b2

/-- ★ **Hoeffding finite-N witness** — N = 1, 2 closed forms. -/
theorem hoeffding_finiteN_witness (negArg : Nat → Nat → Bool) :
    E213.Lib.Math.Probability.Inequality.Hoeffding.hoeffdingBoundAtDepth negArg 1
      = E213.Lib.Math.Real213.ExpLog.CutExpSeries.expPartialSum negArg 1
    ∧ E213.Lib.Math.Probability.Inequality.Hoeffding.hoeffdingBoundAtDepth negArg 2
        = E213.Lib.Math.Real213.ExpLog.CutExpSeries.expPartialSum negArg 2 :=
  ⟨hoeffdingBound_depth_one negArg, hoeffdingBound_depth_two negArg⟩

/-- ★★★ **Total witness** ★★★ — both closures bundled. -/
theorem total_witness (a1 a2 b1 b2 : Nat) (negArg : Nat → Nat → Bool) :
    (a1 * b1 + a2 * b2) * (a1 * b1 + a2 * b2)
      ≤ (a1 * a1 + a2 * a2) * (b1 * b1 + b2 * b2)
    ∧ E213.Lib.Math.Probability.Inequality.Hoeffding.hoeffdingBoundAtDepth negArg 2
        = E213.Lib.Math.Real213.ExpLog.CutExpSeries.expPartialSum negArg 2 :=
  ⟨cs_2d_le a1 a2 b1 b2, hoeffdingBound_depth_two negArg⟩

end E213.Lib.Math.Tactic.Extras.AggregatorCapstone
