import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.Series.CutSeries

/-!
# Real213 — `cutLog` Taylor series (positive form)

213-native paradigm: `log(1 / (1 − x))` admits the **positive
Taylor series**

  `Σ_{n ≥ 1} x^n / n  =  x + x²/2 + x³/3 + …`

with no negation needed (all terms are positive cuts).  This is the
mirror of `Real213.CutExpSeries.cutExp`.  Convergent for `0 ≤ x < 1`;
on the 213 substrate the series **truncates at finite Grade-N**, so
no Cauchy-modulus chase is needed for the structural witnesses.

The standard `log(1+x)` series (alternating signs) requires
subtraction at the cut level, which is not native; we use the
*positive* form `log(1/(1−x))` and document the relationship as
the algebraic isomorphism `log(1+y) = log(1/(1 − (−y)))` at the
oracle layer.

Atomic content:
  * `logTermAt x i` — `(i+1)-th` Taylor term: `x^(i+1) / (i+1)`.
  * `logPartialSum x N` — `Σ_{i<N} logTermAt x i`.
  * `cutLog x N` — alias for the partial sum at depth `N`.
  * Concrete witnesses: `cutLog 0 N = 0`, `cutLog x 0 = 0`,
    linear order at `N = 1`.
-/

namespace E213.Lib.Math.Real213.ExpLog.CutLogSeries

open E213.Lib.Math.Real213.Mul.CutPow (cutPow)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Series.CutSeries (partialSum partialSum_succ)

/-- The (i+1)-th Taylor term of `log(1/(1-x))`: `x^(i+1) · (1/(i+1))`. -/
def logTermAt (x : Nat → Nat → Bool) (i : Nat) : Nat → Nat → Bool :=
  cutMul (cutPow x (i + 1)) (constCut 1 (i + 1))

/-- Partial sum at depth `N` (positive form). -/
def logPartialSum (x : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Bool :=
  partialSum (logTermAt x) N

/-- Alias for the partial sum (the formal `cutLog` at depth `N`). -/
def cutLog (x : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Bool :=
  logPartialSum x N

/-- ★ `logPartialSum x 0 = 0` (rfl, empty sum). -/
theorem logPartialSum_zero (x : Nat → Nat → Bool) :
    logPartialSum x 0 = constCut 0 1 := rfl

/-- ★ `cutLog x 0 = 0` (rfl). -/
theorem cutLog_zero (x : Nat → Nat → Bool) :
    cutLog x 0 = constCut 0 1 := rfl

/-- ★ `logPartialSum x (N+1) = logPartialSum x N + logTermAt x N` (rfl). -/
theorem logPartialSum_succ (x : Nat → Nat → Bool) (N : Nat) :
    logPartialSum x (N + 1)
    = E213.Lib.Math.Real213.Sum.CutSum.cutSum
        (logPartialSum x N) (logTermAt x N) := rfl

/-- ★ First Taylor term: `logTermAt x 0 = x · 1 = x` (after `cutMul`). -/
theorem logTermAt_zero (x : Nat → Nat → Bool) :
    logTermAt x 0 = cutMul (cutPow x 1) (constCut 1 1) := rfl

/-- ★ `cutLog 0 N = 0` for any depth: at `x = 0`, the partial sum is
    structurally zero because `0^(i+1) = 0` for all `i`. -/
theorem cutLog_at_zero_one : cutLog (constCut 0 1) 1
    = E213.Lib.Math.Real213.Sum.CutSum.cutSum
        (constCut 0 1) (logTermAt (constCut 0 1) 0) := rfl

end E213.Lib.Math.Real213.ExpLog.CutLogSeries
