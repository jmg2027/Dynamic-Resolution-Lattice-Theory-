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
  omega

theorem decicIsDifferentiable_derivative_modulus (k : Nat) :
    decicIsDifferentiable.derivativeSmooth.linearityModulus k = 9 * k := by
  show max (quinticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quinticIsDifferentiable.linearityModulus k)
           (quinticIsDifferentiable.linearityModulus k
            + quinticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 9 * k
  rw [quinticIsDifferentiable_derivative_modulus,
      quinticIsDifferentiable_modulus]
  omega

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
  omega

theorem hexadecicIsDifferentiable_derivative_modulus (k : Nat) :
    hexadecicIsDifferentiable.derivativeSmooth.linearityModulus k = 15 * k := by
  show max (octicIsDifferentiable.derivativeSmooth.linearityModulus k
            + octicIsDifferentiable.linearityModulus k)
           (octicIsDifferentiable.linearityModulus k
            + octicIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 15 * k
  rw [octicIsDifferentiable_derivative_modulus, octicIsDifferentiable_modulus]
  omega

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
