import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumOne
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# 213-native ordinary differential equations — propositional solutions

The simplest classes of ODEs solvable propositionally in 213 native
form (no rational-coefficient computation needed):

  y' = 0          → y = constant
  y' = a/b        → y = (a/b)·x  (cutScale)
  y' = 1          → y = id
  y' = 1/2        → y = x/2  (cutHalf)
  y' = a          → y = ax + b  (linear with intercept)
  y'' = 0         → y = ax + b  (second-order, all linears)

Higher-order RHS (`y' = ax`, `y' = x²`, …) require cohomEquiv since
the solution involves rational coefficients beyond constants.

## Sub-namespaces (preserved for cross-file `open` declarations)

  * `E213.Lib.Math.Analysis.ODELinear`      — first-order: y' = a → y = ax + b
  * `E213.Lib.Math.Analysis.ODECatalog`     — pointwise catalog (5 trivial RHS)
  * `E213.Lib.Math.Analysis.ODESecondOrder` — y'' = 0 (linear functions)

( from 3 ODELinear [] +
ODECatalog [] + ODESecondOrder [].  Per-stage
capstone bundles dropped.)
-/

namespace E213.Lib.Math.Analysis.ODELinear

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (cutScaleIsDifferentiable)
open E213.Lib.Math.Real213.Sum.CutSumOne (cutSum_const_zero)

/-- Linear function `y = ax + b` (constant intercept). -/
def linearWithIntercept (a b : Nat) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  fun x => cutSum (cutScale a 1 x) (constCut b 1)

/-- `linearWithIntercept` is differentiable. -/
def linearWithIntercept_isDifferentiable (a b : Nat) :
    IsDifferentiable (linearWithIntercept a b) :=
  addIsDifferentiable (cutScaleIsDifferentiable a 1)
                      (constIsDifferentiable (constCut b 1))

/-- Derivative of `y = ax + b` is constant `a` (pointwise PURE). -/
theorem linearWithIntercept_derivative_at (a b : Nat)
    (t : Nat → Nat → Bool) (m k : Nat) :
    (linearWithIntercept_isDifferentiable a b).derivative t m k
      = constCutFn (constCut a 1) t m k := by
  show cutSum (constCut a 1) (constCut 0 1) m k = constCut a 1 m k
  exact cutSum_const_zero a 1 m k

end E213.Lib.Math.Analysis.ODELinear

namespace E213.Lib.Math.Analysis.ODECatalog

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf)
open E213.Lib.Math.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (idIsDifferentiable constIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
  (cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Lib.Math.Analysis.ODELinear
  (linearWithIntercept_isDifferentiable linearWithIntercept_derivative_at)

/-- y' = 0 → y = constant. -/
theorem ode_zero_solution (c : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative = constCutFn (constCut 0 1) := rfl

/-- y' = 1 → y = id. -/
theorem ode_one_solution :
    idIsDifferentiable.derivative = constCutFn (constCut 1 1) := rfl

/-- y' = a/b → y = cutScale a b. -/
theorem ode_rational_solution (a b : Nat) :
    (cutScaleIsDifferentiable a b).derivative
      = constCutFn (constCut a b) := rfl

/-- y' = 1/2 → y = x/2. -/
theorem ode_half_solution :
    cutHalfIsDifferentiable.derivative = constCutFn (constCut 1 2) := rfl

/-- y' = a → y = ax + b (pointwise PURE). -/
theorem ode_constant_a_solution_at (a b : Nat) (t : Nat → Nat → Bool)
    (m k : Nat) :
    (linearWithIntercept_isDifferentiable a b).derivative t m k
      = constCutFn (constCut a 1) t m k :=
  linearWithIntercept_derivative_at a b t m k

end E213.Lib.Math.Analysis.ODECatalog

namespace E213.Lib.Math.Analysis.ODESecondOrder

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable constIsDifferentiable)

/-- Second-derivative witness for linear function. -/
def linearWithIntercept_secondDerivable (a : Nat) :
    IsDifferentiable (constCutFn (constCut a 1)) :=
  constIsDifferentiable (constCut a 1)

/-- d²/dx² [ax + b] = 0. -/
theorem linearWithIntercept_second_derivative (a : Nat) :
    (linearWithIntercept_secondDerivable a).derivative
      = constCutFn (constCut 0 1) := rfl

/-- d²/dx² [id] = 0. -/
theorem id_second_derivative :
    (constIsDifferentiable (constCut 1 1)).derivative
      = constCutFn (constCut 0 1) := rfl

/-- d²/dx² [const c] = 0 (trivially). -/
theorem const_second_derivative (c : Nat → Nat → Bool) :
    (constIsDifferentiable (constCut 0 1)).derivative
      = constCutFn (constCut 0 1) := rfl

end E213.Lib.Math.Analysis.ODESecondOrder
