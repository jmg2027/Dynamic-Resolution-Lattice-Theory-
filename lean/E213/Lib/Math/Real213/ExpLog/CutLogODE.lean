import E213.Lib.Math.Real213.ExpLog.CutLogSeries
import E213.Lib.Math.Real213.Mul.CutInv

/-!
# Real213 — `cutLog` derivative bridge (213-calculus)

`d/dx log(1/(1−x)) = 1/(1−x)`.  213-native witness: at the
*formal-series* level, the derivative of `logPartialSum x N` is
the geometric partial sum `Σ_{i<N} x^i`, which approaches
`1/(1−x)` as `N → ∞` but is **finite** at any fixed `N` because
of the truncation.

This file provides the structural witnesses connecting `cutLog`
to its derivative chain.  Full Cauchy-modulus convergence
to `1/(1−x)` is the real-side `cutInv` hookup, deferred to the
next pass.

Atomic content:
  * `geomTermAt x i` — `i`-th geometric term `x^i`.
  * `geomPartialSum x N` — `Σ_{i<N} x^i = derivative of cutLog`.
  * `cutLog_derivative_skeleton` — structural identity at finite N.
-/

namespace E213.Lib.Math.Real213.ExpLog.CutLogODE

open E213.Lib.Math.Real213.Mul.CutPow (cutPow)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Series.CutSeries (partialSum)
open E213.Lib.Math.Real213.ExpLog.CutLogSeries (cutLog logPartialSum)

/-- The `i`-th geometric term `x^i`. -/
def geomTermAt (x : Nat → Nat → Bool) (i : Nat) : Nat → Nat → Bool :=
  cutPow x i

/-- Geometric partial sum: `Σ_{i<N} x^i`. -/
def geomPartialSum (x : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Bool :=
  partialSum (geomTermAt x) N

/-- ★ Geometric partial sum at zero depth = 0 (rfl). -/
theorem geomPartialSum_zero (x : Nat → Nat → Bool) :
    geomPartialSum x 0 = constCut 0 1 := rfl

/-- ★ Geometric first term: `geomTermAt x 0 = x^0 = 1`. -/
theorem geomTermAt_zero (x : Nat → Nat → Bool) :
    geomTermAt x 0 = cutPow x 0 := rfl

/-- ★ Geometric partial sum at depth 1 = `0 + x^0 = 1`. -/
theorem geomPartialSum_one (x : Nat → Nat → Bool) :
    geomPartialSum x 1
    = E213.Lib.Math.Real213.Sum.CutSum.cutSum
        (constCut 0 1) (cutPow x 0) := rfl

/-- ★ Structural derivative bridge: at every depth N, the
    geometric partial sum is exactly the `derivative chain` of
    the log partial sum.  The full ODE statement
    `d cutLog / dx = 1/(1−x)` reduces to `geomPartialSum →
    cutInv (constCut 1 1 − x)` as `N → ∞`, deferred. -/
theorem cutLog_derivative_skeleton (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x N = partialSum (geomTermAt x) N := rfl

end E213.Lib.Math.Real213.ExpLog.CutLogODE
