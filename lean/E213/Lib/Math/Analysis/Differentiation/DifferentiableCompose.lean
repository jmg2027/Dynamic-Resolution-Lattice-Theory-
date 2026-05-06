import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Lib.Math.Analysis.Differentiation.DifferentiableAffine

import E213.Lib.Math.Real213.Core
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# DifferentiableCompose
composition (chain rule) IsDifferentiable instances.
Demonstrates that composeIsDifferentiable + concrete polynomial
instances yield closed-form moduli via the chain rule.

## Instances

  squareOfSquareIsDifferentiable     : (x²)² ≡ x⁴, modulus = 4k
  squareOfCubeIsDifferentiable       : (x³)² ≡ x⁶, modulus = 6k
  cubeOfSquareIsDifferentiable       : (x²)³ ≡ x⁶, modulus = 6k
-/

namespace E213.Lib.Math.Analysis.Differentiation.DifferentiableCompose

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core (Real213)
open E213.Lib.Math.Real213.CutMul (cutMul)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Lib.Math.Analysis.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)

/-- (x²)²: composition of square with itself.  Same function as
    quarticIsDifferentiable but constructed via chain rule. -/
def squareOfSquareIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  composeIsDifferentiable squareIsDifferentiable squareIsDifferentiable

/-- (x³)²: square of cube. -/
def squareOfCubeIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x (cutMul x x))
                                      (cutMul x (cutMul x x))) :=
  composeIsDifferentiable cubeIsDifferentiable squareIsDifferentiable

/-- (x²)³: cube of square. -/
def cubeOfSquareIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x x)
                                      (cutMul (cutMul x x) (cutMul x x))) :=
  composeIsDifferentiable squareIsDifferentiable cubeIsDifferentiable

/-- (x²)² modulus = 2·(2k) = 4k.  ∅-axiom: Nat213.mul_assoc.symm. -/
theorem squareOfSquare_modulus (k : Nat) :
    squareOfSquareIsDifferentiable.linearityModulus k = 4 * k := by
  show squareIsDifferentiable.linearityModulus
       (squareIsDifferentiable.linearityModulus k) = 4 * k
  rw [squareIsDifferentiable_modulus, squareIsDifferentiable_modulus]
  exact (E213.Tactic.Nat213.mul_assoc 2 2 k).symm

/-- (x³)² modulus = 3·(2k) = 6k.  ∅-axiom. -/
theorem squareOfCube_modulus (k : Nat) :
    squareOfCubeIsDifferentiable.linearityModulus k = 6 * k := by
  show cubeIsDifferentiable.linearityModulus
       (squareIsDifferentiable.linearityModulus k) = 6 * k
  rw [squareIsDifferentiable_modulus, cubeIsDifferentiable_modulus]
  exact (E213.Tactic.Nat213.mul_assoc 3 2 k).symm

/-- (x²)³ modulus = 2·(3k) = 6k.  ∅-axiom. -/
theorem cubeOfSquare_modulus (k : Nat) :
    cubeOfSquareIsDifferentiable.linearityModulus k = 6 * k := by
  show squareIsDifferentiable.linearityModulus
       (cubeIsDifferentiable.linearityModulus k) = 6 * k
  rw [cubeIsDifferentiable_modulus, squareIsDifferentiable_modulus]
  exact (E213.Tactic.Nat213.mul_assoc 2 3 k).symm

/-- capstone: composition modulus = product of degrees. -/
theorem polynomial_compose_capstone (k : Nat) :
    squareOfSquareIsDifferentiable.linearityModulus k = 4 * k
    ∧ squareOfCubeIsDifferentiable.linearityModulus k = 6 * k
    ∧ cubeOfSquareIsDifferentiable.linearityModulus k = 6 * k :=
  ⟨squareOfSquare_modulus k, squareOfCube_modulus k, cubeOfSquare_modulus k⟩

end E213.Lib.Math.Analysis.Differentiation.DifferentiableCompose
