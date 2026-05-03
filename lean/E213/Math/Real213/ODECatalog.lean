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
   linearWithIntercept_derivative linearWithIntercept_derivative_at)

/-- y' = 0: constant function is solution. -/
theorem ode_zero_solution (c : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative = constCutFn (constCut 0 1) := rfl

/-- y' = 1: id is solution. -/
theorem ode_one_solution :
    idIsDifferentiable.derivative = constCutFn (constCut 1 1) := rfl

/-- y' = a/b (general rational constant): cutScale a b is solution. -/
theorem ode_rational_solution (a b : Nat) :
    (cutScaleIsDifferentiable a b).derivative
      = constCutFn (constCut a b) := rfl

/-- y' = 1/2: cutHalf is solution. -/
theorem ode_half_solution :
    cutHalfIsDifferentiable.derivative = constCutFn (constCut 1 2) := rfl

/-- ★ y' = a pointwise (PURE). -/
theorem ode_constant_a_solution_at (a b : Nat) (t : Nat → Nat → Bool)
    (m k : Nat) :
    (linearWithIntercept_isDifferentiable a b).derivative t m k
      = constCutFn (constCut a 1) t m k :=
  linearWithIntercept_derivative_at a b t m k

/-- ★ Phase CV capstone (PURE) — 5 ODE catalog solutions pointwise. -/
theorem ode_catalog_capstone_pure (a b : Nat) (c : Nat → Nat → Bool) :
    (∀ t m k, (constIsDifferentiable c).derivative t m k
              = constCutFn (constCut 0 1) t m k)
    ∧ (∀ t m k, idIsDifferentiable.derivative t m k
                = constCutFn (constCut 1 1) t m k)
    ∧ (∀ t m k, (linearWithIntercept_isDifferentiable a b).derivative t m k
                = constCutFn (constCut a 1) t m k)
    ∧ (∀ t m k, (cutScaleIsDifferentiable a b).derivative t m k
                = constCutFn (constCut a b) t m k)
    ∧ (∀ t m k, cutHalfIsDifferentiable.derivative t m k
                = constCutFn (constCut 1 2) t m k) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl,
   ode_constant_a_solution_at a b,
   fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end E213.Math.Real213.ODECatalog
