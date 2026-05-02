import E213.Math.Real213.PhaseANOmegaCapstone

/-!
# Research.Real213ConcreteDerivativeModulus

Phase AP: concrete polynomial IsDifferentiable instances yield
**tighter** derivative moduli than the generic recursive chain.

For x^n in the concrete chain (squareIsDiff, cubeIsDiff, ...) the
derivative modulus is `(n-1)·k` — matching the actual mathematical
fact that derivative of degree-n polynomial is degree (n-1).

The generic `cutPowFnIsDifferentiable n` chain gives `n·k` due to
structural overhead, so concrete instances are sharper.

## Theorems

  squareIsDifferentiable_derivative_modulus    : k    (= 1·k)
  cubeIsDifferentiable_derivative_modulus      : 2k
  quarticIsDifferentiable_derivative_modulus   : 3k
-/

namespace E213.Math.Real213.ConcreteDerivativeModulus

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)

/-- d/dx [x²] modulus = k (linear, degree 1). -/
theorem squareIsDifferentiable_derivative_modulus (k : Nat) :
    squareIsDifferentiable.derivativeSmooth.linearityModulus k = k := by
  show max (0 + k) (k + 0) = k
  omega

/-- d/dx [x³] modulus = 2k (quadratic, degree 2). -/
theorem cubeIsDifferentiable_derivative_modulus (k : Nat) :
    cubeIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k := by
  show max (0 + squareIsDifferentiable.linearityModulus k)
           (k + squareIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 2 * k
  rw [squareIsDifferentiable_modulus,
      squareIsDifferentiable_derivative_modulus]
  omega

/-- d/dx [x⁴] modulus = 3k (cubic, degree 3). -/
theorem quarticIsDifferentiable_derivative_modulus (k : Nat) :
    quarticIsDifferentiable.derivativeSmooth.linearityModulus k = 3 * k := by
  show max (squareIsDifferentiable.derivativeSmooth.linearityModulus k
            + squareIsDifferentiable.linearityModulus k)
           (squareIsDifferentiable.linearityModulus k
            + squareIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 3 * k
  rw [squareIsDifferentiable_derivative_modulus,
      squareIsDifferentiable_modulus]
  omega

/-- Phase AP capstone: concrete polynomial chain has degree-1
    derivative modulus (sharper than generic n·k). -/
theorem concrete_polynomial_derivative_modulus_sharp (k : Nat) :
    squareIsDifferentiable.derivativeSmooth.linearityModulus k = k
    ∧ cubeIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k
    ∧ quarticIsDifferentiable.derivativeSmooth.linearityModulus k = 3 * k :=
  ⟨squareIsDifferentiable_derivative_modulus k,
   cubeIsDifferentiable_derivative_modulus k,
   quarticIsDifferentiable_derivative_modulus k⟩

end E213.Math.Real213.ConcreteDerivativeModulus
