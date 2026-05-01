import E213.Math.Real213.DifferentiableAffine

/-!
# Research.Real213DifferentiableCompose

Phase AJ: composition (chain rule) IsDifferentiable instances.
Demonstrates that composeIsDifferentiable + concrete polynomial
instances yield closed-form moduli via the chain rule.

## Instances

  squareOfSquareIsDifferentiable     : (x²)² ≡ x⁴, modulus = 4k
  squareOfCubeIsDifferentiable       : (x³)² ≡ x⁶, modulus = 6k
  cubeOfSquareIsDifferentiable       : (x²)³ ≡ x⁶, modulus = 6k
-/

namespace E213.Math.Real213.DifferentiableCompose

open E213.Firmware E213.Hypervisor

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

/-- (x²)² modulus = 2·(2k) = 4k. -/
theorem squareOfSquare_modulus (k : Nat) :
    squareOfSquareIsDifferentiable.linearityModulus k = 4 * k := by
  show squareIsDifferentiable.linearityModulus
       (squareIsDifferentiable.linearityModulus k) = 4 * k
  rw [squareIsDifferentiable_modulus, squareIsDifferentiable_modulus]
  omega

/-- (x³)² modulus = cube_mod(square_mod k) = 3·(2k) = 6k. -/
theorem squareOfCube_modulus (k : Nat) :
    squareOfCubeIsDifferentiable.linearityModulus k = 6 * k := by
  show cubeIsDifferentiable.linearityModulus
       (squareIsDifferentiable.linearityModulus k) = 6 * k
  rw [squareIsDifferentiable_modulus, cubeIsDifferentiable_modulus]
  omega

/-- (x²)³ modulus = square_mod(cube_mod k) = 2·(3k) = 6k. -/
theorem cubeOfSquare_modulus (k : Nat) :
    cubeOfSquareIsDifferentiable.linearityModulus k = 6 * k := by
  show squareIsDifferentiable.linearityModulus
       (cubeIsDifferentiable.linearityModulus k) = 6 * k
  rw [cubeIsDifferentiable_modulus, squareIsDifferentiable_modulus]
  omega

/-- Phase AJ capstone: composition modulus = product of degrees. -/
theorem polynomial_compose_capstone (k : Nat) :
    squareOfSquareIsDifferentiable.linearityModulus k = 4 * k
    ∧ squareOfCubeIsDifferentiable.linearityModulus k = 6 * k
    ∧ cubeOfSquareIsDifferentiable.linearityModulus k = 6 * k :=
  ⟨squareOfSquare_modulus k, squareOfCube_modulus k, cubeOfSquare_modulus k⟩

end E213.Math.Real213.DifferentiableCompose
