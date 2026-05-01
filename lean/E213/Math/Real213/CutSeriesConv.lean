import E213.Math.Real213.CutSeries
import E213.Math.Real213.CutPow

/-!
# Research.Real213CutSeriesConv: series convergence theorems

Generic ratio test + comparison test framework.

## Definition

Convergent: SeriesCauchy is well-defined.
RatioBound: |a_{n+1}| ≤ r * |a_n| for some r < 1, eventually.
ComparisonBound: |a_n| ≤ b_n.
-/

namespace E213.Math.Real213.CutSeriesConv

open E213.Firmware E213.Hypervisor

/-- **Convergent series**: wrapper for SeriesCauchy. -/
abbrev ConvergentSeries := SeriesCauchy

/-- **RatioBound** (declarative): |a_{n+1}| ≤ r * |a_n| eventually. -/
structure RatioBound (terms : Nat → Nat → Nat → Bool)
    (r_num r_den : Nat) where
  N : Nat  -- after this index, bound holds
  bound_data : Unit  -- placeholder for explicit bound proof

/-- **ComparisonBound** (declarative): |a_n| ≤ b_n. -/
structure ComparisonBound (terms_a terms_b : Nat → Nat → Nat → Bool) where
  bound_at : Nat → Unit  -- placeholder

end E213.Math.Real213.CutSeriesConv

namespace E213.Math.Real213.CutSeriesConv

open E213.Firmware E213.Hypervisor

/-- **Ratio test scaffold**: if |a_{n+1}/a_n| ≤ r < 1 eventually,
    series converges.  Full proof requires geometric bound + Cauchy
    completeness — separate arc.  This module is an interface. -/
def ratioTestScaffold (terms : Nat → Nat → Nat → Bool)
    (r_num r_den : Nat) (rb : RatioBound terms r_num r_den) :
    Unit := ()

/-- **Comparison test scaffold**. -/
def comparisonTestScaffold (a b : Nat → Nat → Nat → Bool)
    (cb : ComparisonBound a b) (b_conv : SeriesCauchy) :
    Unit := ()

/-- **Geometric series convergence (declarative)**: Σ r^i converges if
    r < 1.  Full SeriesCauchy construction is separate. -/
structure GeometricConvergent (r_num r_den : Nat) where
  ratio_lt_one : r_num < r_den
  series_data : Unit  -- placeholder for explicit Cauchy data

end E213.Math.Real213.CutSeriesConv
