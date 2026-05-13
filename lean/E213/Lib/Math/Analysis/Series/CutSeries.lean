import E213.Lib.Math.Analysis.Series.CutSequence
import E213.Lib.Math.Real213.Mul.CutAlgebraic

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# Real213CutSeries: series convergence framework

Iterated partial sums + Cauchy form for series.

## Definition

partialSum s : Nat → RealCut — partial sums Σ_{i<n} s i.
SeriesCauchy: explicit modulus form.
-/

namespace E213.Lib.Math.Analysis.Series.CutSeries

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- **partialSum**: Σ_{i<n} s i, defined recursively. -/
def partialSum (s : Nat → (Nat → Nat → Bool)) : Nat → (Nat → Nat → Bool)
  | 0 => constCut 0 1
  | n+1 => cutSum (partialSum s n) (s n)

/-- **SeriesCauchy**: Cauchy series with explicit modulus. -/
structure SeriesCauchy where
  terms : Nat → (Nat → Nat → Bool)
  N : Nat → Nat → Nat
  cauchy : ∀ m k, ∀ i j, i ≥ N m k → j ≥ N m k →
    partialSum terms i m k = partialSum terms j m k

/-- Series limit (cut). -/
def SeriesCauchy.limit (sc : SeriesCauchy) : Nat → Nat → Bool :=
  fun m k => partialSum sc.terms (sc.N m k) m k

/-- Constant zero series. -/
def zeroSeries : Nat → (Nat → Nat → Bool) :=
  fun _ => constCut 0 1

/-- partialSum of zero series at 0 = 0-cut. -/
example : partialSum zeroSeries 0 = constCut 0 1 := rfl

/-- partialSum unfolding at 0 (rfl). -/
theorem partialSum_zero_unfold (s : Nat → (Nat → Nat → Bool)) :
    partialSum s 0 = constCut 0 1 := rfl

/-- partialSum unfolding at n+1 (rfl). -/
theorem partialSum_succ (s : Nat → (Nat → Nat → Bool)) (n : Nat) :
    partialSum s (n+1) = cutSum (partialSum s n) (s n) := rfl

end E213.Lib.Math.Analysis.Series.CutSeries
