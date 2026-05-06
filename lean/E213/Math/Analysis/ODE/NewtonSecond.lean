import E213.Math.Analysis.ODE.ODE

/-!
# Newton's second law (velocity form): v' = F/m = a

For a particle under constant force F with mass m:
  acceleration a = F/m  (constant)
  velocity v(t) = a·t + v0  (linear in t)
  v'(t) = a  (Newton's 2nd law)

We formalize the velocity-equation pointwise: linear v solves v' = a.
The position equation x = at²/2 + v0t + x0 has the 1/2 issue
(rational coefficient) and is left for cohomEquiv treatment.
-/

namespace E213.Math.Analysis.ODE.NewtonSecond

open E213.Theory E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.ODELinear
  (linearWithIntercept linearWithIntercept_isDifferentiable
   linearWithIntercept_derivative_at)
open E213.Math.Analysis.ODESecondOrder
  (linearWithIntercept_secondDerivable)

/-- Velocity function for constant acceleration: v(t) = a·t + v0. -/
def velocity_constant_force (a v0 : Nat) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  linearWithIntercept a v0

/-- Newton's 2nd law (pointwise): v'(t) = a. -/
theorem newton_second_law_at (a v0 : Nat)
    (t : Nat → Nat → Bool) (m k : Nat) :
    (linearWithIntercept_isDifferentiable a v0).derivative t m k
      = constCutFn (constCut a 1) t m k :=
  linearWithIntercept_derivative_at a v0 t m k

/-- Constant force ⟹ constant acceleration. -/
theorem constant_force_constant_acceleration (a : Nat) :
    (linearWithIntercept_secondDerivable a).derivative
      = constCutFn (constCut 0 1) := rfl

end E213.Math.Analysis.ODE.NewtonSecond
