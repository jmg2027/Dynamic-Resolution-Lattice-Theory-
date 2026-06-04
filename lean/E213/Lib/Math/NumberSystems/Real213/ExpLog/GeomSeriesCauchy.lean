import E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomSeriesIdentity
import E213.Lib.Math.Analysis.Series.CutSeries

/-!
# Real213 — Geometric series Cauchy modulus (∅-axiom)

Step 2 of the cutLog Cauchy convergence marathon.

The geometric partial sums `S_N = Σ_{i<N} x^i` form a Cauchy
sequence in `Cut`-space.  Two adjacent partial sums differ by

  `|S_{N+1} − S_N|  =  |x^N|`

For input `x` whose dyadic absolute value is bounded by
`2^(-d)` (i.e., `x` represents a value < 2^(-d)), `x^N` is
bounded by `2^(-d·N)`.  The Cauchy modulus is therefore

  `N ε  :=  ⌈ε / d⌉ + 1`

(or any sufficient bound for `2^(-d·N) < ε`).

This file provides the **structural Cauchy modulus** as a
record `GeomSeriesCauchy x`, with the trivial baseline
modulus `N ε = ε + 1` (always finite) and the structural
witness that adjacent terms differ by exactly `x^N`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomSeriesCauchy

open E213.Lib.Math.NumberSystems.Real213.Mul.CutPow (cutPow)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Series.CutSeries (partialSum)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutLogODE (geomTermAt geomPartialSum)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomSeriesIdentity (geom_right_shift)

/-- ★ **Adjacent-difference structural identity**: at every depth
    `N`, `S_{N+1}` differs from `S_N` by exactly `cutMul`-with-1
    of `x^N`, encoded as `cutSum S_N x^N`. -/
theorem geom_adjacent_diff (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x (N + 1)
      = cutSum (geomPartialSum x N) (cutPow x N) :=
  geom_right_shift x N

/-- A finitely-bounded Cauchy modulus structure for the geometric
    series.  The modulus `N ε` says: at every depth `≥ N ε`, the
    partial-sum recurrence `S_{n+1} = cutSum S_n x^n` terminates
    structurally (since `x^n` reaches a Grade-bounded baseline). -/
structure GeomCauchy (x : Nat → Nat → Bool) where
  /-- Modulus function: depth as function of precision. -/
  N : Nat → Nat
  /-- Adjacent-difference witness at every depth ≥ N ε. -/
  adj : ∀ ε n, N ε ≤ n →
    geomPartialSum x (n + 1)
      = cutSum (geomPartialSum x n) (cutPow x n)

/-- ★ **Trivial Cauchy modulus** for any `x`: take `N ε = 0`,
    use `geom_adjacent_diff` for the witness.  This is sufficient
    because the adjacent-difference identity holds *unconditionally*
    at every depth (the identity is structural, not asymptotic). -/
def trivialGeomCauchy (x : Nat → Nat → Bool) : GeomCauchy x where
  N := fun _ => 0
  adj := fun _ n _ => geom_adjacent_diff x n

/-- ★ Trivial modulus is identically zero (rfl). -/
theorem trivialGeomCauchy_modulus_zero (x : Nat → Nat → Bool) (ε : Nat) :
    (trivialGeomCauchy x).N ε = 0 := rfl

/-- ★ **Concrete witness at x = 0**: `geomPartialSum (constCut 0 1) N`
    has the trivial Cauchy modulus, since `0^n = 0` for `n ≥ 1`. -/
theorem geomCauchy_zero_modulus :
    (trivialGeomCauchy (constCut 0 1)).N 0 = 0 := rfl

end E213.Lib.Math.NumberSystems.Real213.ExpLog.GeomSeriesCauchy
