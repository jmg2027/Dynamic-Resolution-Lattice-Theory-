import E213.Research.Real213.DifferentiableCompose
import E213.Research.Real213.ConcreteDerivativeMega

/-!
# Research.Real213ComposeDerivativeModulus

Phase AU: derivative resolution depth for composed (chain-rule)
polynomial instances.  By the chain rule d/dx [g∘f] = g'(f(x))·f'(x),
the derivative is a product of (g'∘f) and f', so its modulus is
sum of those.

  d/dx [(x²)²] = 2(x²)·2x ≡ 4x³  modulus = 3k (= 4-1)
  d/dx [(x³)²] = 2(x³)·3x² ≡ 6x⁵ modulus = 5k (= 6-1)
  d/dx [(x²)³] = 3(x²)²·2x ≡ 6x⁵ modulus = 5k (= 6-1)
-/

namespace E213.Research.Real213.ComposeDerivativeModulus

open E213.Firmware E213.Hypervisor

/-- d/dx [(x²)²] modulus = 3k via chain rule. -/
theorem squareOfSquare_derivative_modulus (k : Nat) :
    squareOfSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 3 * k := by
  show squareIsDifferentiable.linearityModulus
       (squareIsDifferentiable.derivativeSmooth.linearityModulus k)
       + squareIsDifferentiable.derivativeSmooth.linearityModulus k = 3 * k
  rw [squareIsDifferentiable_derivative_modulus,
      squareIsDifferentiable_modulus]
  omega

/-- d/dx [(x³)²] modulus = 5k via chain rule. -/
theorem squareOfCube_derivative_modulus (k : Nat) :
    squareOfCubeIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k := by
  show cubeIsDifferentiable.linearityModulus
       (squareIsDifferentiable.derivativeSmooth.linearityModulus k)
       + cubeIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k
  rw [squareIsDifferentiable_derivative_modulus,
      cubeIsDifferentiable_modulus,
      cubeIsDifferentiable_derivative_modulus]
  omega

/-- d/dx [(x²)³] modulus = 5k via chain rule. -/
theorem cubeOfSquare_derivative_modulus (k : Nat) :
    cubeOfSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k := by
  show squareIsDifferentiable.linearityModulus
       (cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       + squareIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k
  rw [cubeIsDifferentiable_derivative_modulus,
      squareIsDifferentiable_modulus,
      squareIsDifferentiable_derivative_modulus]
  omega

/-- Phase AU capstone: chain-rule derivative moduli. -/
theorem compose_derivative_capstone (k : Nat) :
    squareOfSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 3 * k
    ∧ squareOfCubeIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k
    ∧ cubeOfSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k :=
  ⟨squareOfSquare_derivative_modulus k,
   squareOfCube_derivative_modulus k,
   cubeOfSquare_derivative_modulus k⟩

end E213.Research.Real213.ComposeDerivativeModulus
