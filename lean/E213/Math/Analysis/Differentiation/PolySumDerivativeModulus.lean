import E213.Math.NatHelpers.Max213
import E213.Math.Analysis.Differentiation.DifferentiableAffine
import E213.Kernel.Tactic.Omega213

import E213.Math.Analysis.Differentiation.ConcreteDerivativeModulus
import E213.Math.Real213.Core
import E213.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Math.Analysis.Differentiation.Differentiable
/-!
# PolySumDerivativeModulus
derivative resolution depth for polynomial sums (degree-n
polynomial + lower degree).  The derivative of x² + x is 2x + 1
(linear), and the framework produces modulus = k matching the
mathematical degree.

## Theorems

  affineIsDifferentiable_derivative_modulus       : 0 (constant slope)
  squarePlusIdIsDifferentiable_derivative_modulus : k (linear deriv of x²+x)
  cubePlusSquareIsDifferentiable_derivative_modulus : 2k (quadratic deriv)
-/

namespace E213.Math.Analysis.Differentiation.PolySumDerivativeModulus

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus)
open E213.Math.Analysis.Differentiation.DifferentiableAffine
  (affineIsDifferentiable squarePlusIdIsDifferentiable
   cubePlusSquareIsDifferentiable
   affineIsDifferentiable_modulus squarePlusIdIsDifferentiable_modulus
   cubePlusSquareIsDifferentiable_modulus)
open E213.Math.Analysis.Differentiation.ConcreteDerivativeModulus
  (squareIsDifferentiable_derivative_modulus
   cubeIsDifferentiable_derivative_modulus
   quarticIsDifferentiable_derivative_modulus)

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
  cases k with
  | zero => rfl
  | succ n => rfl

/-- d/dx [x³ + x²] modulus = 2k (quadratic derivative 3x² + 2x). -/
theorem cubePlusSquareIsDifferentiable_derivative_modulus (k : Nat) :
    cubePlusSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
           (squareIsDifferentiable.derivativeSmooth.linearityModulus k) = 2 * k
  rw [cubeIsDifferentiable_derivative_modulus,
      squareIsDifferentiable_derivative_modulus]
  -- 2*k = k + k by Nat.two_mul.  max (k+k) k = k+k since k ≤ k+k.
  rw [Nat.two_mul]
  show max (k + k) k = k + k
  cases k with
  | zero => rfl
  | succ n =>
    -- (n+1) + (n+1) ≥ (n+1).  max picks the larger.
    show (if (n+1) + (n+1) ≤ n+1 then n+1 else (n+1) + (n+1))
         = (n+1) + (n+1)
    have hge : ¬ ((n+1) + (n+1) ≤ n+1) := fun h => by
      have : n + 1 + (n+1) ≥ n + 1 + 1 :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le n)) (n+1)
      exact Nat.not_succ_le_self (n+1) (Nat.le_trans this h)
    exact if_neg hge

/-- capstone: polynomial sum derivative moduli match
    expected degree (= max of constituent derivative degrees). -/
theorem polynomial_sum_derivative_capstone (a b k : Nat) :
    (affineIsDifferentiable a b).derivativeSmooth.linearityModulus k = 0
    ∧ squarePlusIdIsDifferentiable.derivativeSmooth.linearityModulus k = k
    ∧ cubePlusSquareIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k :=
  ⟨affineIsDifferentiable_derivative_modulus a b k,
   squarePlusIdIsDifferentiable_derivative_modulus k,
   cubePlusSquareIsDifferentiable_derivative_modulus k⟩

end E213.Math.Analysis.Differentiation.PolySumDerivativeModulus
