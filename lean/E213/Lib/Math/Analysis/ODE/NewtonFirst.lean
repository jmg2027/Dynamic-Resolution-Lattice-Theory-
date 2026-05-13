import E213.Lib.Math.Analysis.ODE.ODE

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# NewtonFirst
★ Newton's first law in 213 native form ★

Newton's first law: F = 0 → constant velocity.  In ODE form:
  x''(t) = a(t) = F(t)/m = 0  (zero force)
  x'(t) = v0  (constant velocity)
  x(t)  = v0 t + x0  (linear position)

Our framework formalizes this propEq:
  - position: linearWithIntercept v0 x0
  - velocity: derivative = constCutFn (constCut v0 1)
  - acceleration: second derivative = 0
-/

namespace E213.Lib.Math.Analysis.ODE.NewtonFirst

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.ODELinear
  (linearWithIntercept linearWithIntercept_isDifferentiable
   linearWithIntercept_derivative_at)
open E213.Lib.Math.Analysis.ODESecondOrder
  (linearWithIntercept_secondDerivable)

/-- ★ Position function for constant velocity motion: x(t) = v0·t + x0. -/
def position_constant_velocity (v0 x0 : Nat) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  linearWithIntercept v0 x0

/-- ★ Acceleration = 0 (Newton's first law: no force). -/
theorem acceleration_is_zero (v0 : Nat) :
    (linearWithIntercept_secondDerivable v0).derivative
      = constCutFn (constCut 0 1) := rfl

/-- ★ Velocity = v0 pointwise (PURE). -/
theorem velocity_is_v0_at (v0 x0 : Nat) (t : Nat → Nat → Bool) (m k : Nat) :
    (linearWithIntercept_isDifferentiable v0 x0).derivative t m k
      = constCut v0 1 m k :=
  linearWithIntercept_derivative_at v0 x0 t m k

/-- ★ capstone (PURE) — Newton's first law pointwise. -/
theorem newton_first_law_capstone_pure (v0 x0 : Nat) :
    (∀ t m k, (linearWithIntercept_isDifferentiable v0 x0).derivative t m k
              = constCutFn (constCut v0 1) t m k)
    ∧ (∀ t m k, (linearWithIntercept_isDifferentiable v0 x0).derivative t m k
                = constCut v0 1 m k)
    ∧ (linearWithIntercept_secondDerivable v0).derivative
        = constCutFn (constCut 0 1) :=
  ⟨linearWithIntercept_derivative_at v0 x0,
   velocity_is_v0_at v0 x0,
   rfl⟩

end E213.Lib.Math.Analysis.ODE.NewtonFirst
