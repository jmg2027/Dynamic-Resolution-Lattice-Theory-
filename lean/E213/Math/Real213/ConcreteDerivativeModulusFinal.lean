import E213.Math.Real213.ConcreteDerivativeModulusHigh

/-!
# Research.Real213ConcreteDerivativeModulusFinal

Phase AR: completing the (n-1)·k pattern for high-order polynomials
9, 10, 12, 16.

  d/dx [x⁹]  modulus = 8k
  d/dx [x¹⁰] modulus = 9k
  d/dx [x¹²] modulus = 11k
  d/dx [x¹⁶] modulus = 15k
-/

namespace E213.Math.Real213.ConcreteDerivativeModulusFinal

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
open E213.Math.Real213.DifferentiableHighOrder
  (nonicIsDifferentiable decicIsDifferentiable dodecicIsDifferentiable
   hexadecicIsDifferentiable
   nonicIsDifferentiable_modulus decicIsDifferentiable_modulus
   dodecicIsDifferentiable_modulus hexadecicIsDifferentiable_modulus)
open E213.Math.Real213.ConcreteDerivativeModulus
  (squareIsDifferentiable_derivative_modulus
   cubeIsDifferentiable_derivative_modulus
   quarticIsDifferentiable_derivative_modulus)
open E213.Math.Real213.ConcreteDerivativeModulusHigh
  (quinticIsDifferentiable_derivative_modulus
   sexticIsDifferentiable_derivative_modulus
   septicIsDifferentiable_derivative_modulus
   octicIsDifferentiable_derivative_modulus)

/-- Helper: a*k + b*k = (a+b)*k. -/
private theorem coef_add (a b k : Nat) : a * k + b * k = (a + b) * k :=
  (E213.Tactic.Nat213.add_mul a b k).symm

theorem nonicIsDifferentiable_derivative_modulus (k : Nat) :
    nonicIsDifferentiable.derivativeSmooth.linearityModulus k = 8 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quinticIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + quinticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 8 * k
  rw [quarticIsDifferentiable_derivative_modulus,
      quinticIsDifferentiable_modulus,
      quarticIsDifferentiable_modulus,
      quinticIsDifferentiable_derivative_modulus]
  rw [coef_add 3 5 k, coef_add 4 4 k]
  exact Nat.max_self (8 * k)

theorem decicIsDifferentiable_derivative_modulus (k : Nat) :
    decicIsDifferentiable.derivativeSmooth.linearityModulus k = 9 * k := by
  show max (quinticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quinticIsDifferentiable.linearityModulus k)
           (quinticIsDifferentiable.linearityModulus k
            + quinticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 9 * k
  rw [quinticIsDifferentiable_derivative_modulus,
      quinticIsDifferentiable_modulus]
  rw [coef_add 4 5 k, coef_add 5 4 k]
  exact Nat.max_self (9 * k)

theorem dodecicIsDifferentiable_derivative_modulus (k : Nat) :
    dodecicIsDifferentiable.derivativeSmooth.linearityModulus k = 11 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + octicIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + octicIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 11 * k
  rw [quarticIsDifferentiable_derivative_modulus,
      octicIsDifferentiable_modulus,
      quarticIsDifferentiable_modulus,
      octicIsDifferentiable_derivative_modulus]
  rw [coef_add 3 8 k, coef_add 4 7 k]
  exact Nat.max_self (11 * k)

theorem hexadecicIsDifferentiable_derivative_modulus (k : Nat) :
    hexadecicIsDifferentiable.derivativeSmooth.linearityModulus k = 15 * k := by
  show max (octicIsDifferentiable.derivativeSmooth.linearityModulus k
            + octicIsDifferentiable.linearityModulus k)
           (octicIsDifferentiable.linearityModulus k
            + octicIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 15 * k
  rw [octicIsDifferentiable_derivative_modulus, octicIsDifferentiable_modulus]
  rw [coef_add 7 8 k, coef_add 8 7 k]
  exact Nat.max_self (15 * k)

/-- Phase AR capstone: concrete derivative modulus high orders. -/
theorem concrete_higher_polynomial_derivative_capstone (k : Nat) :
    nonicIsDifferentiable.derivativeSmooth.linearityModulus k = 8 * k
    ∧ decicIsDifferentiable.derivativeSmooth.linearityModulus k = 9 * k
    ∧ dodecicIsDifferentiable.derivativeSmooth.linearityModulus k = 11 * k
    ∧ hexadecicIsDifferentiable.derivativeSmooth.linearityModulus k = 15 * k :=
  ⟨nonicIsDifferentiable_derivative_modulus k,
   decicIsDifferentiable_derivative_modulus k,
   dodecicIsDifferentiable_derivative_modulus k,
   hexadecicIsDifferentiable_derivative_modulus k⟩

end E213.Math.Real213.ConcreteDerivativeModulusFinal
