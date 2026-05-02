import E213.Math.Real213.ODESecondOrder

/-!
# Research.Real213NewtonFirst

Phase CX: ★ Newton's first law in 213 native form ★

Newton's first law: F = 0 → constant velocity.  In ODE form:
  x''(t) = a(t) = F(t)/m = 0  (zero force)
  x'(t) = v0  (constant velocity)
  x(t)  = v0 t + x0  (linear position)

Our framework formalizes this propEq:
  - position: linearWithIntercept v0 x0
  - velocity: derivative = constCutFn (constCut v0 1)
  - acceleration: second derivative = 0
-/

namespace E213.Math.Real213.NewtonFirst

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★ Position function for constant velocity motion: x(t) = v0·t + x0. -/
def position_constant_velocity (v0 x0 : Nat) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  linearWithIntercept v0 x0

/-- ★ Velocity is the (constant) derivative of position. -/
theorem velocity_is_v0 (v0 x0 : Nat) :
    (linearWithIntercept_isDifferentiable v0 x0).derivative
      = constCutFn (constCut v0 1) :=
  linearWithIntercept_derivative v0 x0

/-- ★ Acceleration = 0 (Newton's first law: no force). -/
theorem acceleration_is_zero (v0 : Nat) :
    (linearWithIntercept_secondDerivable v0).derivative
      = constCutFn (constCut 0 1) := rfl

/-- Phase CX capstone: Newton's first law formalized. -/
theorem newton_first_law_capstone (v0 x0 : Nat) (t : Nat → Nat → Bool) :
    -- (1) Position function is differentiable
    (linearWithIntercept_isDifferentiable v0 x0).derivative
        = constCutFn (constCut v0 1)
    -- (2) Velocity is constant v0 at any t
    ∧ (linearWithIntercept_isDifferentiable v0 x0).derivative t
        = constCut v0 1
    -- (3) Acceleration is 0 (no force)
    ∧ (linearWithIntercept_secondDerivable v0).derivative
        = constCutFn (constCut 0 1) :=
  ⟨linearWithIntercept_derivative v0 x0,
   by rw [velocity_is_v0]; rfl,
   rfl⟩

end E213.Math.Real213.NewtonFirst
