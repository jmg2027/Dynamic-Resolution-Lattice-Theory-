import E213.Research.Real213.IsDifferentiable

/-!
# Research.Real213DerivativeForms: closed-form derivative theorems

Phase AD-2: rfl-clean closed forms for the `IsDifferentiable.derivative`
field of each constructor.  These give a computational handle for
Phase AD-3 (difference-quotient bound).

## Theorems

  id_derivative_form        : d/dx [x]    = 1 as constCutFn
  const_derivative_form     : d/dx [c]    = 0 as constCutFn
  add_derivative_form       : d/dx [f+g]  = f' + g' (pointwise)
  mul_derivative_form       : d/dx [f·g]  = f'·g + f·g' (product rule)
  compose_derivative_form   : d/dx [g∘f]  = g'(f(x))·f'(x) (chain rule)
  cutPow0_derivative_form   : d/dx [x^0]  = 0
  cutPow_derivative_step    : recurrence for d/dx [x^(n+1)]
-/

namespace E213.Research.Real213.DerivativeForms

open E213.Firmware E213.Hypervisor

/-- d/dx [x] = 1 as a constant function. -/
theorem id_derivative_form :
    idIsDifferentiable.derivative = constCutFn (constCut 1 1) := rfl

/-- d/dx [c] = 0 as a constant function. -/
theorem const_derivative_form (c : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative = constCutFn (constCut 0 1) := rfl

/-- Sum-rule pointwise form: d/dx [f+g] (x) = f'(x) + g'(x). -/
theorem add_derivative_form {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) (x : Nat → Nat → Bool) :
    (addIsDifferentiable sf sg).derivative x
      = cutSum (sf.derivative x) (sg.derivative x) := rfl

/-- Product-rule pointwise form: d/dx [f·g] (x) = f'(x)·g(x) + f(x)·g'(x). -/
theorem mul_derivative_form {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) (x : Nat → Nat → Bool) :
    (mulIsDifferentiable sf sg).derivative x
      = cutSum (cutMul (sf.derivative x) (g x))
               (cutMul (f x) (sg.derivative x)) := rfl

/-- Chain-rule pointwise form: d/dx [g∘f] (x) = g'(f(x)) · f'(x). -/
theorem compose_derivative_form {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) (x : Nat → Nat → Bool) :
    (composeIsDifferentiable sf sg).derivative x
      = cutMul (sg.derivative (f x)) (sf.derivative x) := rfl

/-- d/dx [x^0] = 0. -/
theorem cutPow0_derivative_form :
    (cutPowFnIsDifferentiable 0).derivative = constCutFn (constCut 0 1) := rfl

/-- Recurrence for d/dx [x^(n+1)] via product rule on cutPow x n · x. -/
theorem cutPow_derivative_step (n : Nat) (x : Nat → Nat → Bool) :
    (cutPowFnIsDifferentiable (n+1)).derivative x
      = cutSum (cutMul ((cutPowFnIsDifferentiable n).derivative x) x)
               (cutMul (cutPow x n) (constCut 1 1)) := rfl

/-- Concrete: d/dx [x] evaluated at any point is constCut 1 1. -/
example (x : Nat → Nat → Bool) :
    idIsDifferentiable.derivative x = constCut 1 1 := rfl

/-- Concrete: d/dx [c] evaluated at any point is constCut 0 1. -/
example (c x : Nat → Nat → Bool) :
    (constIsDifferentiable c).derivative x = constCut 0 1 := rfl

end E213.Research.Real213.DerivativeForms
