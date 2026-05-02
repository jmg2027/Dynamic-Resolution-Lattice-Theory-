import E213.Math.Real213.ConcreteDerivativeModulus

/-!
# Research.Real213ConcreteDerivativeModulusHigh

Phase AQ: extending Phase AP to degrees 5-8.

  d/dx [x⁵] modulus = 4k
  d/dx [x⁶] modulus = 5k
  d/dx [x⁷] modulus = 6k
  d/dx [x⁸] modulus = 7k

Pattern: derivative of x^n has modulus (n-1)·k.
-/

namespace E213.Math.Real213.ConcreteDerivativeModulusHigh

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Math.Real213.ConcreteDerivativeModulus
  (squareIsDifferentiable_derivative_modulus
   cubeIsDifferentiable_derivative_modulus
   quarticIsDifferentiable_derivative_modulus)

/-- Helper: a*k + b*k = (a+b)*k via Nat213.add_mul.symm. -/
private theorem coef_add (a b k : Nat) :
    a * k + b * k = (a + b) * k :=
  (E213.Tactic.Nat213.add_mul a b k).symm

theorem quinticIsDifferentiable_derivative_modulus (k : Nat) :
    quinticIsDifferentiable.derivativeSmooth.linearityModulus k = 4 * k := by
  show max (squareIsDifferentiable.derivativeSmooth.linearityModulus k
            + cubeIsDifferentiable.linearityModulus k)
           (squareIsDifferentiable.linearityModulus k
            + cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 4 * k
  rw [squareIsDifferentiable_derivative_modulus, cubeIsDifferentiable_modulus,
      squareIsDifferentiable_modulus, cubeIsDifferentiable_derivative_modulus]
  -- max (k + 3*k) (2*k + 2*k) = 4*k
  have hL : k + 3 * k = 4 * k := by
    have e := coef_add 1 3 k
    rw [Nat.one_mul] at e
    exact e
  have hR : 2 * k + 2 * k = 4 * k := coef_add 2 2 k
  rw [hL, hR]
  exact Nat.max_self (4 * k)

theorem sexticIsDifferentiable_derivative_modulus (k : Nat) :
    sexticIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k
            + cubeIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k
            + cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 5 * k
  rw [cubeIsDifferentiable_derivative_modulus, cubeIsDifferentiable_modulus]
  rw [coef_add 2 3 k, coef_add 3 2 k]
  exact Nat.max_self (5 * k)

theorem septicIsDifferentiable_derivative_modulus (k : Nat) :
    septicIsDifferentiable.derivativeSmooth.linearityModulus k = 6 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k
            + quarticIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k
            + quarticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 6 * k
  rw [cubeIsDifferentiable_derivative_modulus, quarticIsDifferentiable_modulus,
      cubeIsDifferentiable_modulus, quarticIsDifferentiable_derivative_modulus]
  rw [coef_add 2 4 k, coef_add 3 3 k]
  exact Nat.max_self (6 * k)

theorem octicIsDifferentiable_derivative_modulus (k : Nat) :
    octicIsDifferentiable.derivativeSmooth.linearityModulus k = 7 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quarticIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + quarticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 7 * k
  rw [quarticIsDifferentiable_derivative_modulus, quarticIsDifferentiable_modulus]
  rw [coef_add 3 4 k, coef_add 4 3 k]
  exact Nat.max_self (7 * k)

theorem concrete_high_polynomial_derivative_capstone (k : Nat) :
    quinticIsDifferentiable.derivativeSmooth.linearityModulus k = 4 * k
    ∧ sexticIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k
    ∧ septicIsDifferentiable.derivativeSmooth.linearityModulus k = 6 * k
    ∧ octicIsDifferentiable.derivativeSmooth.linearityModulus k = 7 * k :=
  ⟨quinticIsDifferentiable_derivative_modulus k,
   sexticIsDifferentiable_derivative_modulus k,
   septicIsDifferentiable_derivative_modulus k,
   octicIsDifferentiable_derivative_modulus k⟩

end E213.Math.Real213.ConcreteDerivativeModulusHigh
