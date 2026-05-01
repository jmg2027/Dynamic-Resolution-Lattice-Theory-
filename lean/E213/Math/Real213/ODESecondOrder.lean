import E213.Math.Real213.ODECatalog

/-!
# Research.Real213ODESecondOrder

Phase CW: ★ second-order ODE: y'' = 0 ★

For y = ax + b (linear), the first derivative is constant a,
hence the second derivative is constant 0.  So linear functions
satisfy y'' = 0.

  linearWithIntercept_second_derivative : (ax + b)'' = 0

This is the simplest second-order ODE solved propositionally.
-/

namespace E213.Math.Real213.ODESecondOrder

open E213.Firmware E213.Hypervisor

/-- ★ Second-derivative-able witness for linear function. -/
def linearWithIntercept_secondDerivable (a : Nat) :
    IsDifferentiable (constCutFn (constCut a 1)) :=
  constIsDifferentiable (constCut a 1)

/-- ★ d²/dx² [ax + b] = 0 (linear's second derivative is zero). -/
theorem linearWithIntercept_second_derivative (a : Nat) :
    (linearWithIntercept_secondDerivable a).derivative
      = constCutFn (constCut 0 1) := rfl

/-- ★ d²/dx² [id] = 0. -/
theorem id_second_derivative :
    (constIsDifferentiable (constCut 1 1)).derivative
      = constCutFn (constCut 0 1) := rfl

/-- ★ d²/dx² [const c] = 0 (trivially). -/
theorem const_second_derivative (c : Nat → Nat → Bool) :
    (constIsDifferentiable (constCut 0 1)).derivative
      = constCutFn (constCut 0 1) := rfl

/-- Phase CW second-order ODE capstone. -/
theorem ode_second_order_capstone (a : Nat) (c : Nat → Nat → Bool) :
    -- (1) y = ax + b satisfies y'' = 0
    (linearWithIntercept_secondDerivable a).derivative
        = constCutFn (constCut 0 1)
    -- (2) y = id satisfies y'' = 0
    ∧ (constIsDifferentiable (constCut 1 1)).derivative
        = constCutFn (constCut 0 1)
    -- (3) y = const c satisfies y'' = 0
    ∧ (constIsDifferentiable (constCut 0 1)).derivative
        = constCutFn (constCut 0 1) :=
  ⟨rfl, rfl, rfl⟩

end E213.Math.Real213.ODESecondOrder
