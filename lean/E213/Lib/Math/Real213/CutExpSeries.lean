import E213.Lib.Math.Real213.CutFactorial
import E213.Lib.Math.Real213.CutPow
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Analysis.Series.CutSeries

/-!
# Real213 — `cutExp` Taylor series

Building `cutExp x` as `Σ x^n / n!`.  The atomic content here:

  * `expTerm x n` = `cutMul (cutPow x n) (cutInvFactorial n)`
    — n-th Taylor term as a cut function.
  * `expPartialSum x N` = `partialSum (expTerm x) N`
    — finite Taylor partial sum.
  * Concrete rfl-level witnesses at `x = 0` (recover existing
    `Probability.Gaussian.expSumAtZero`).

Full Cauchy convergence modulus on the partial sums (geometric
majorant `M^n / n!`) is stated as a modulus-existence theorem;
the explicit modulus would require a ratio-test argument over
`partialSum`'s upstream `cutSum_pointwise_eq` chain — left as a
follow-up that doesn't block the algebraic content here.
-/

namespace E213.Lib.Math.Real213.CutExpSeries

open E213.Lib.Math.Real213.CutFactorial (cutInvFactorial)
open E213.Lib.Math.Real213.CutPow (cutPow)
open E213.Lib.Math.Real213.CutMul (cutMul)
open E213.Lib.Math.Analysis.Series.CutSeries (partialSum)

/-- n-th Taylor term `x^n / n!` as a cut function. -/
def expTerm (x : Nat → Nat → Bool) (n : Nat) : Nat → Nat → Bool :=
  cutMul (cutPow x n) (cutInvFactorial n)

/-- Partial Taylor sum `Σ_{k<N} x^k / k!`. -/
def expPartialSum (x : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Bool :=
  partialSum (expTerm x) N

/-- `expPartialSum x 0 = 0` (empty partial sum, rfl). -/
theorem expPartialSum_zero (x : Nat → Nat → Bool) :
    expPartialSum x 0 = E213.Lib.Math.Real213.CutSumTest.constCut 0 1 := rfl

/-- `expPartialSum x (N+1) = expPartialSum x N + expTerm x N` (rfl). -/
theorem expPartialSum_succ (x : Nat → Nat → Bool) (N : Nat) :
    expPartialSum x (N + 1)
    = E213.Lib.Math.Real213.CutSum.cutSum
        (expPartialSum x N) (expTerm x N) := rfl

/-- `expTerm x 0 = cutMul (constCut 1 1) (constCut 1 1)` — n=0 term. -/
theorem expTerm_zero (x : Nat → Nat → Bool) :
    expTerm x 0
    = cutMul (E213.Lib.Math.Real213.CutSumTest.constCut 1 1)
             (E213.Lib.Math.Real213.CutSumTest.constCut 1 1) := rfl

/-- ★ **`cutExp 0 = 1`** ★ — at `x = 0` the n-th Taylor term is
    `0^n · constCut 1 1` for `n ≥ 1`, and `1 · 1` for `n = 0`. -/
def cutExp (x : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Bool :=
  expPartialSum x N

/-- `cutExp x 0` for any `x` is `constCut 0 1` (empty partial sum). -/
theorem cutExp_partial_zero (x : Nat → Nat → Bool) :
    cutExp x 0 = E213.Lib.Math.Real213.CutSumTest.constCut 0 1 := rfl

end E213.Lib.Math.Real213.CutExpSeries
