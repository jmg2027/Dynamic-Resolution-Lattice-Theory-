import E213.Math.Real213.DifferentiableInstances
import E213.Math.Real213.IntegralProperties

/-!
# Research.Real213ODELinear

Phase CU: ★ linear ODE solutions ★

For y' = a (constant), the solution is y = ax + b for any
intercept b.  In our framework:

  cutScale a 1 + constCutFn (constCut b 1) is differentiable
  with derivative = constCutFn (constCut a 1)

This is the simplest first-order ODE solved propositionally
in 213 native form.
-/

namespace E213.Math.Real213.ODELinear

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutPow (cutScale)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Math.Real213.Antiderivative (IsAntiderivative)
open E213.Math.Real213.CutSumOne (cutSum_const_zero)

/-- ★ Linear function y = ax + b (constant intercept). -/
def linearWithIntercept (a b : Nat) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  fun x => cutSum (cutScale a 1 x) (constCut b 1)

/-- ★ Linear function is IsDifferentiable. -/
def linearWithIntercept_isDifferentiable (a b : Nat) :
    IsDifferentiable (linearWithIntercept a b) :=
  addIsDifferentiable (cutScaleIsDifferentiable a 1)
                      (constIsDifferentiable (constCut b 1))

/-- ★ Derivative of y = ax + b is constant a, pointwise (PURE). -/
theorem linearWithIntercept_derivative_at (a b : Nat)
    (t : Nat → Nat → Bool) (m k : Nat) :
    (linearWithIntercept_isDifferentiable a b).derivative t m k
      = constCutFn (constCut a 1) t m k := by
  show cutSum (constCut a 1) (constCut 0 1) m k = constCut a 1 m k
  exact cutSum_const_zero a 1 m k

/-- ★ Phase CU capstone (PURE) — pointwise linear ODE. -/
theorem linear_ode_capstone_at (a b : Nat) :
    (∀ t m k, (linearWithIntercept_isDifferentiable a b).derivative t m k
              = constCutFn (constCut a 1) t m k)
    ∧ (∀ t m k, idIsDifferentiable.derivative t m k
                = constCutFn (constCut 1 1) t m k) :=
  ⟨linearWithIntercept_derivative_at a b,
   fun _ _ _ => rfl⟩

end E213.Math.Real213.ODELinear
