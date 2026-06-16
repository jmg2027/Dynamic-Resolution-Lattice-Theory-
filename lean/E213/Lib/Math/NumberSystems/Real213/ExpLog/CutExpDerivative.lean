import E213.Lib.Math.Analysis.Differentiation.Differentiable
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries

/-!
# CutExpDerivative — cut-level differentiation of the exp Taylor series (∅-axiom)

Rung T3 of the transcendental-functions ladder (`research-notes/frontiers/
transcendentals/transcendental_functions_ladder.md`), at the **function-space**
level: the exp Taylor partial sum `Σ_{k<N} xᵏ/k!` is differentiable *as a function
of the cut `x`*, and its derivative is the term-by-term derivative sum.

This is the first cut-level (function-space) differentiation result for a *series*
(the existing `Differentiable` instances cover a fixed polynomial degree, not a
sum-over-N).  It is ∅-axiom **by construction**: the `IsDifferentiable.derivative`
field is definitional data composed from the sum/product/power rules, so the
termwise law is `rfl` — it needs no cut re-association, side-stepping both the
signed-cut subtraction wall (alternating sin/cos) and the `cutSum`-assoc `b≥3`
wall that block the *limit-level* identities.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpDerivative

open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable addIsDifferentiable mulIsDifferentiable
   constIsDifferentiable cutPowFnIsDifferentiable)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries (expTerm expPartialSum)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (cutInvFactorial)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- The `n`-th Taylor term `xⁿ/n!` is differentiable in `x`: `cutPow x n` times the
    constant `cutInvFactorial n`, via the product rule. -/
def expTermIsDifferentiable (n : Nat) : IsDifferentiable (fun x => expTerm x n) :=
  mulIsDifferentiable (cutPowFnIsDifferentiable n)
                      (constIsDifferentiable (cutInvFactorial n))

/-- ★★★ **The exp Taylor partial sum is differentiable in `x`** — a finite sum of
    differentiable terms, for every truncation `N`.  The first cut-level
    differentiation of a series (not a fixed-degree polynomial). -/
def expPartialSumIsDifferentiable : ∀ N, IsDifferentiable (fun x => expPartialSum x N)
  | 0     => constIsDifferentiable (constCut 0 1)
  | N + 1 => addIsDifferentiable (expPartialSumIsDifferentiable N)
                                 (expTermIsDifferentiable N)

/-- ★★ **Termwise differentiation** (`rfl`): the derivative of the `(N+1)`-truncated
    Taylor sum is the derivative of the `N`-truncation plus the derivative of the
    `N`-th term — `d/dx [Σ_{k<N+1} xᵏ/k!] = d/dx[Σ_{k<N} xᵏ/k!] + d/dx[xᴺ/N!]`.
    Holds definitionally because the derivative field is the sum-rule composition. -/
theorem expPartialSum_derivative_termwise (N : Nat) (x : Nat → Nat → Bool) :
    (expPartialSumIsDifferentiable (N + 1)).derivative x
      = cutSum ((expPartialSumIsDifferentiable N).derivative x)
               ((expTermIsDifferentiable N).derivative x) := rfl

end E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpDerivative
