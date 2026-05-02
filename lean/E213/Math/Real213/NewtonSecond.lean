import E213.Math.Real213.PhaseDAOmegaOmega

/-!
# Research.Real213NewtonSecond

Phase DB: ★ Newton's second law (velocity form): v' = F/m = a ★

For a particle under constant force F with mass m:
  acceleration a = F/m  (constant)
  velocity v(t) = a·t + v0  (linear in t)
  v'(t) = a  (Newton's 2nd law)

We formalize the velocity-equation: linear v solves v' = a propEq.
The position equation x = at²/2 + v0t + x0 has the 1/2 issue
(rational coefficient) and is left for cohomEquiv treatment.
-/

namespace E213.Math.Real213.NewtonSecond

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★ Velocity function for constant acceleration: v(t) = a·t + v0. -/
def velocity_constant_force (a v0 : Nat) :
    (Nat → Nat → Bool) → (Nat → Nat → Bool) :=
  linearWithIntercept a v0

/-- ★ Newton's 2nd law: v'(t) = a (constant acceleration). -/
theorem newton_second_law (a v0 : Nat) :
    (linearWithIntercept_isDifferentiable a v0).derivative
      = constCutFn (constCut a 1) :=
  linearWithIntercept_derivative a v0

/-- ★ Velocity at any time t equals constant a (post-derivative). -/
theorem velocity_derivative_at (a v0 : Nat) (t : Nat → Nat → Bool) :
    (linearWithIntercept_isDifferentiable a v0).derivative t
      = constCut a 1 := by
  rw [newton_second_law]; rfl

/-- ★ Force = mass × acceleration → constant force ⟹ constant acceleration. -/
theorem constant_force_constant_acceleration (a v0 : Nat) (t : Nat → Nat → Bool) :
    (linearWithIntercept_secondDerivable a).derivative t
      = constCut 0 1 := rfl

/-- Phase DB capstone: Newton's 2nd law (velocity equation). -/
theorem newton_second_capstone (a v0 : Nat) (t : Nat → Nat → Bool) :
    -- (1) v(t) is differentiable
    (linearWithIntercept_isDifferentiable a v0).derivative
        = constCutFn (constCut a 1)
    -- (2) v'(t) = a at every t
    ∧ (linearWithIntercept_isDifferentiable a v0).derivative t = constCut a 1
    -- (3) Acceleration = a constant
    ∧ (linearWithIntercept_secondDerivable a).derivative t = constCut 0 1 :=
  ⟨newton_second_law a v0,
   velocity_derivative_at a v0 t,
   rfl⟩

end E213.Math.Real213.NewtonSecond
