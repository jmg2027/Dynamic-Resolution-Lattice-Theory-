import E213.Research.Real213ConcreteDerivativeModulus

/-!
# Research.Real213ConcreteDerivativeModulusHigh

Phase AQ: extending Phase AP to degrees 5-8.

  d/dx [x⁵] modulus = 4k
  d/dx [x⁶] modulus = 5k
  d/dx [x⁷] modulus = 6k
  d/dx [x⁸] modulus = 7k

Pattern: derivative of x^n has modulus (n-1)·k.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

theorem quinticIsDifferentiable_derivative_modulus (k : Nat) :
    quinticIsDifferentiable.derivativeSmooth.linearityModulus k = 4 * k := by
  show max (squareIsDifferentiable.derivativeSmooth.linearityModulus k
            + cubeIsDifferentiable.linearityModulus k)
           (squareIsDifferentiable.linearityModulus k
            + cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 4 * k
  rw [squareIsDifferentiable_derivative_modulus, cubeIsDifferentiable_modulus,
      squareIsDifferentiable_modulus, cubeIsDifferentiable_derivative_modulus]
  omega

theorem sexticIsDifferentiable_derivative_modulus (k : Nat) :
    sexticIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k
            + cubeIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k
            + cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 5 * k
  rw [cubeIsDifferentiable_derivative_modulus, cubeIsDifferentiable_modulus]
  omega

theorem septicIsDifferentiable_derivative_modulus (k : Nat) :
    septicIsDifferentiable.derivativeSmooth.linearityModulus k = 6 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k
            + quarticIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k
            + quarticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 6 * k
  rw [cubeIsDifferentiable_derivative_modulus, quarticIsDifferentiable_modulus,
      cubeIsDifferentiable_modulus, quarticIsDifferentiable_derivative_modulus]
  omega

theorem octicIsDifferentiable_derivative_modulus (k : Nat) :
    octicIsDifferentiable.derivativeSmooth.linearityModulus k = 7 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quarticIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + quarticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 7 * k
  rw [quarticIsDifferentiable_derivative_modulus, quarticIsDifferentiable_modulus]
  omega

theorem concrete_high_polynomial_derivative_capstone (k : Nat) :
    quinticIsDifferentiable.derivativeSmooth.linearityModulus k = 4 * k
    ∧ sexticIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k
    ∧ septicIsDifferentiable.derivativeSmooth.linearityModulus k = 6 * k
    ∧ octicIsDifferentiable.derivativeSmooth.linearityModulus k = 7 * k :=
  ⟨quinticIsDifferentiable_derivative_modulus k,
   sexticIsDifferentiable_derivative_modulus k,
   septicIsDifferentiable_derivative_modulus k,
   octicIsDifferentiable_derivative_modulus k⟩

end E213.Research.Real213CutSum
