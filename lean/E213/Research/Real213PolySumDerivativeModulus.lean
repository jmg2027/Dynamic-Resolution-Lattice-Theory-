import E213.Research.Real213DifferentiableAffine
import E213.Research.Real213ConcreteDerivativeMega

/-!
# Research.Real213PolySumDerivativeModulus

Phase AT: derivative resolution depth for polynomial sums (degree-n
polynomial + lower degree).  The derivative of x² + x is 2x + 1
(linear), and the framework produces modulus = k matching the
mathematical degree.

## Theorems

  affineIsDifferentiable_derivative_modulus       : 0 (constant slope)
  squarePlusIdIsDifferentiable_derivative_modulus : k (linear deriv of x²+x)
  cubePlusSquareIsDifferentiable_derivative_modulus : 2k (quadratic deriv)
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- d/dx [a·x + b] modulus = 0 (derivative is constant a). -/
theorem affineIsDifferentiable_derivative_modulus (a b k : Nat) :
    (affineIsDifferentiable a b).derivativeSmooth.linearityModulus k = 0 := by
  show max 0 0 = 0
  rfl

/-- d/dx [x² + x] modulus = k (linear derivative 2x + 1). -/
theorem squarePlusIdIsDifferentiable_derivative_modulus (k : Nat) :
    squarePlusIdIsDifferentiable.derivativeSmooth.linearityModulus k = k := by
  show max (squareIsDifferentiable.derivativeSmooth.linearityModulus k)
           (idIsDifferentiable.derivativeSmooth.linearityModulus k) = k
  rw [squareIsDifferentiable_derivative_modulus]
  show max k 0 = k
  omega

/-- d/dx [x³ + x²] modulus = 2k (quadratic derivative 3x² + 2x). -/
theorem cubePlusSquareIsDifferentiable_derivative_modulus (k : Nat) :
    cubePlusSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
           (squareIsDifferentiable.derivativeSmooth.linearityModulus k) = 2 * k
  rw [cubeIsDifferentiable_derivative_modulus,
      squareIsDifferentiable_derivative_modulus]
  exact Nat.max_eq_left (by omega)

/-- Phase AT capstone: polynomial sum derivative moduli match
    expected degree (= max of constituent derivative degrees). -/
theorem polynomial_sum_derivative_capstone (a b k : Nat) :
    (affineIsDifferentiable a b).derivativeSmooth.linearityModulus k = 0
    ∧ squarePlusIdIsDifferentiable.derivativeSmooth.linearityModulus k = k
    ∧ cubePlusSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k :=
  ⟨affineIsDifferentiable_derivative_modulus a b k,
   squarePlusIdIsDifferentiable_derivative_modulus k,
   cubePlusSquareIsDifferentiable_derivative_modulus k⟩

end E213.Research.Real213CutSum
