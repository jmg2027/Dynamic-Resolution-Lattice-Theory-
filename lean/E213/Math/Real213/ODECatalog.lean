import E213.Math.Real213.ODELinear

/-!
# Research.Real213ODECatalog

Phase CV: ★ ODE solutions catalog — propEq solutions for trivial RHS.

  y' = 0          → y = constant
  y' = 1          → y = id (or any cutScale 1 1 form)
  y' = a          → y = ax + b (linear)
  y' = constant c → y = constant intercept-anti

These are the simplest ODEs solvable propositionally in 213.
Higher-order RHS (y' = ax, y' = x², etc.) require cohomEquiv since
the solution involves rational coefficients.
-/

namespace E213.Math.Real213.ODECatalog

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutHalf)
open E213.Math.Real213.CutPow (cutScale)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.IsDifferentiable
  (idIsDifferentiable constIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Real213.ODELinear
  (linearWithIntercept_isDifferentiable
   linearWithIntercept_derivative)

/-- y' = 0: constant function is solution. -/
theorem ode_zero_solution (c : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative = constCutFn (constCut 0 1) := rfl

/-- y' = 1: id is solution. -/
theorem ode_one_solution :
    idIsDifferentiable.derivative = constCutFn (constCut 1 1) := rfl

/-- y' = a (constant a): linear function ax + b is solution. -/
theorem ode_constant_a_solution (a b : Nat) :
    (linearWithIntercept_isDifferentiable a b).derivative
      = constCutFn (constCut a 1) :=
  linearWithIntercept_derivative a b

/-- y' = a/b (general rational constant): cutScale a b is solution. -/
theorem ode_rational_solution (a b : Nat) :
    (cutScaleIsDifferentiable a b).derivative
      = constCutFn (constCut a b) := rfl

/-- y' = 1/2: cutHalf is solution. -/
theorem ode_half_solution :
    cutHalfIsDifferentiable.derivative = constCutFn (constCut 1 2) := rfl

/-- ★ Phase CV ODE catalog capstone: 5 trivial ODE solutions. -/
theorem ode_catalog_capstone (a b : Nat) (c : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative = constCutFn (constCut 0 1)
    ∧ idIsDifferentiable.derivative = constCutFn (constCut 1 1)
    ∧ (linearWithIntercept_isDifferentiable a b).derivative
        = constCutFn (constCut a 1)
    ∧ (cutScaleIsDifferentiable a b).derivative
        = constCutFn (constCut a b)
    ∧ cutHalfIsDifferentiable.derivative = constCutFn (constCut 1 2) :=
  ⟨rfl, rfl, ode_constant_a_solution a b, rfl, rfl⟩

end E213.Math.Real213.ODECatalog
