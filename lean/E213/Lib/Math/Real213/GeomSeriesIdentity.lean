import E213.Lib.Math.Real213.CutLogODE
import E213.Lib.Math.Real213.CutPow
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Analysis.Series.CutSeries

/-!
# Real213 — Geometric series structural identity (∅-axiom)

Step 1 of the cutLog Cauchy convergence marathon.

In ZFC, the geometric series identity is

  `Σ_{i<N} x^i = (1 − x^N) / (1 − x)`

which gives `1/(1−x)` as `N → ∞` for `|x| < 1`.  In 213-native
terms, sub at the cut layer is not native; we work with the
**additive shift identity**

  `cutSum (x^N) (Σ_{i<N} x^i) = Σ_{i<N+1} x^i = cutSum (Σ_{i<N} x^i) (x^N)`

which is `partialSum_succ` plus `cutSum` commutativity, *and*
the **left-shift recurrence**

  `cutSum (cutPow x 0) (cutMul x (Σ_{i<N} x^i)) = Σ_{i<N+1} x^i`

which gives the algebraic structure that, in the limit, becomes
the fixpoint equation `S = 1 + x · S`, i.e., `S = 1/(1−x)`.

This file provides the structural witnesses at finite N.
-/

namespace E213.Lib.Math.Real213.GeomSeriesIdentity

open E213.Lib.Math.Real213.CutPow (cutPow cutPow_zero cutPow_succ)
open E213.Lib.Math.Real213.CutMul (cutMul)
open E213.Lib.Math.Real213.CutSum (cutSum)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Series.CutSeries
  (partialSum partialSum_succ)
open E213.Lib.Math.Real213.CutLogODE
  (geomTermAt geomPartialSum geomPartialSum_zero geomPartialSum_one)

/-- ★ **Right-shift identity** at every depth N (rfl): the
    partial sum recurrence
    `S_{N+1} = cutSum S_N (x^N)`. -/
theorem geom_right_shift (x : Nat → Nat → Bool) (N : Nat) :
    geomPartialSum x (N + 1)
      = cutSum (geomPartialSum x N) (cutPow x N) :=
  partialSum_succ (geomTermAt x) N

/-- ★ **Geometric partial sum at depth 0 = 0** (rfl). -/
theorem geom_depth_zero (x : Nat → Nat → Bool) :
    geomPartialSum x 0 = constCut 0 1 := rfl

/-- ★ **At depth 1 = `0 + x^0 = 1`** (rfl). -/
theorem geom_depth_one (x : Nat → Nat → Bool) :
    geomPartialSum x 1 = cutSum (constCut 0 1) (cutPow x 0) := rfl

/-- ★ **At depth 2 = `S_1 + x^1` (rfl). -/
theorem geom_depth_two (x : Nat → Nat → Bool) :
    geomPartialSum x 2
      = cutSum (geomPartialSum x 1) (cutPow x 1) := rfl

/-- ★ **Term-at recurrence**: `geomTermAt x (i+1) = cutMul (geomTermAt x i) x`. -/
theorem geomTermAt_succ (x : Nat → Nat → Bool) (i : Nat) :
    geomTermAt x (i + 1) = cutMul (geomTermAt x i) x := rfl

/-- ★ **Term-at zero**: `geomTermAt x 0 = constCut 1 1` (rfl). -/
theorem geomTermAt_zero (x : Nat → Nat → Bool) :
    geomTermAt x 0 = constCut 1 1 := rfl

end E213.Lib.Math.Real213.GeomSeriesIdentity
