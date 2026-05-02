import E213.Math.Real213.DifferentiableHighOrder

/-!
# Research.Real213DifferentiableMid

Phase AL: midpoint combinator for IsDifferentiable.

If f, g are differentiable, then mid(f, g)(x) = (f(x) + g(x))/2 is
also differentiable, with derivative = mid(f', g') = (f' + g')/2.

## Theorems

  midIsDifferentiable          combinator
  mid_derivative_form          d/dx [mid(f,g)] = mid(f',g')
  midIsDifferentiable_modulus  modulus = max (sf.mod) (sg.mod)
-/

namespace E213.Math.Real213.DifferentiableMid

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.IsSmooth (midIsSmooth)

/-- Midpoint combinator: (f+g)/2 is differentiable, derivative = (f'+g')/2. -/
def midIsDifferentiable {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) :
    IsDifferentiable (fun x => cutMid (f x) (g x)) where
  toIsSmooth := midIsSmooth sf.toIsSmooth sg.toIsSmooth
  derivative := fun x => cutMid (sf.derivative x) (sg.derivative x)
  derivativeSmooth := midIsSmooth sf.derivativeSmooth sg.derivativeSmooth

/-- d/dx [mid(f, g)] (x) = mid(f'(x), g'(x)). -/
theorem mid_derivative_form {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) (x : Nat → Nat → Bool) :
    (midIsDifferentiable sf sg).derivative x
      = cutMid (sf.derivative x) (sg.derivative x) := rfl

/-- Midpoint modulus: max of constituent moduli. -/
theorem midIsDifferentiable_modulus {f g} (sf : IsDifferentiable f)
    (sg : IsDifferentiable g) (k : Nat) :
    (midIsDifferentiable sf sg).linearityModulus k
      = max (sf.linearityModulus k) (sg.linearityModulus k) := rfl

/-- Concrete: mid(x², x³) is differentiable with modulus = max(2k, 3k) = 3k. -/
def midSquareCubeIsDifferentiable :
    IsDifferentiable (fun x => cutMid (cutMul x x) (cutMul x (cutMul x x))) :=
  midIsDifferentiable squareIsDifferentiable cubeIsDifferentiable

/-- mid(x², x³) modulus = 3k. -/
theorem midSquareCube_modulus (k : Nat) :
    midSquareCubeIsDifferentiable.linearityModulus k = 3 * k := by
  show max (squareIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k) = 3 * k
  rw [squareIsDifferentiable_modulus, cubeIsDifferentiable_modulus]
  exact Nat.max_eq_right (by omega)

/-- Concrete: mid(id, x²) modulus = max(k, 2k) = 2k. -/
def midIdSquareIsDifferentiable :
    IsDifferentiable (fun x => cutMid x (cutMul x x)) :=
  midIsDifferentiable idIsDifferentiable squareIsDifferentiable

/-- mid(id, x²) modulus = 2k. -/
theorem midIdSquare_modulus (k : Nat) :
    midIdSquareIsDifferentiable.linearityModulus k = 2 * k := by
  show max k (squareIsDifferentiable.linearityModulus k) = 2 * k
  rw [squareIsDifferentiable_modulus]
  exact Nat.max_eq_right (by omega)

/-- Phase AL capstone: mid combinator + concrete instances. -/
theorem midpoint_capstone (k : Nat) :
    midSquareCubeIsDifferentiable.linearityModulus k = 3 * k
    ∧ midIdSquareIsDifferentiable.linearityModulus k = 2 * k :=
  ⟨midSquareCube_modulus k, midIdSquare_modulus k⟩

end E213.Math.Real213.DifferentiableMid
