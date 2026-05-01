import E213.Research.Real213.DifferentiationCapstone

/-!
# Research.Real213DifferentiableAffine

Phase AI: affine and polynomial-sum IsDifferentiable instances using
`addIsDifferentiable`.  Useful for ML-style polynomial models like
f(x) = ax + b or f(x) = x² + ax + b.

## Instances

  affineIsDifferentiable (a b)        : x ↦ a·x + b,  modulus = k
  squarePlusIdIsDifferentiable        : x ↦ x² + x,   modulus = 2k
  squarePlusAffineIsDifferentiable    : x ↦ x² + ax + b
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- x ↦ a·x + b: linear scaling + constant offset. -/
def affineIsDifferentiable (a b : Nat) :
    IsDifferentiable (fun x => cutSum (cutScale a 1 x)
                                      ((constCutFn (constCut b 1)) x)) :=
  addIsDifferentiable (cutScaleIsDifferentiable a 1)
                      (constIsDifferentiable (constCut b 1))

/-- d/dx [a·x + b] = a + 0 = a (structural). -/
theorem affine_derivative_form (a b : Nat) (x : Nat → Nat → Bool) :
    (affineIsDifferentiable a b).derivative x
      = cutSum (constCut a 1) (constCut 0 1) := rfl

/-- Affine modulus: max k 0 = k (linear). -/
theorem affineIsDifferentiable_modulus (a b k : Nat) :
    (affineIsDifferentiable a b).linearityModulus k = k := by
  show max k 0 = k
  exact Nat.max_eq_left (Nat.zero_le _)

/-- x ↦ x² + x. -/
def squarePlusIdIsDifferentiable :
    IsDifferentiable (fun x => cutSum (cutMul x x) x) :=
  addIsDifferentiable squareIsDifferentiable idIsDifferentiable

/-- Modulus: max (2k) k = 2k. -/
theorem squarePlusIdIsDifferentiable_modulus (k : Nat) :
    squarePlusIdIsDifferentiable.linearityModulus k = 2 * k := by
  show max (squareIsDifferentiable.linearityModulus k) k = 2 * k
  rw [squareIsDifferentiable_modulus]
  exact Nat.max_eq_left (by omega)

/-- d/dx [x² + x] = (1·x + x·1) + 1. -/
theorem squarePlusId_derivative_form (x : Nat → Nat → Bool) :
    squarePlusIdIsDifferentiable.derivative x
      = cutSum (cutSum (cutMul (constCut 1 1) x) (cutMul x (constCut 1 1)))
               (constCut 1 1) := rfl

/-- x ↦ x³ + x² (cubic + quadratic). -/
def cubePlusSquareIsDifferentiable :
    IsDifferentiable (fun x => cutSum (cutMul x (cutMul x x)) (cutMul x x)) :=
  addIsDifferentiable cubeIsDifferentiable squareIsDifferentiable

/-- Modulus: max (3k) (2k) = 3k. -/
theorem cubePlusSquareIsDifferentiable_modulus (k : Nat) :
    cubePlusSquareIsDifferentiable.linearityModulus k = 3 * k := by
  show max (cubeIsDifferentiable.linearityModulus k)
           (squareIsDifferentiable.linearityModulus k) = 3 * k
  rw [cubeIsDifferentiable_modulus, squareIsDifferentiable_modulus]
  exact Nat.max_eq_left (by omega)

/-- Phase AI capstone: polynomial sum moduli. -/
theorem polynomial_sum_capstone (a b k : Nat) :
    (affineIsDifferentiable a b).linearityModulus k = k
    ∧ squarePlusIdIsDifferentiable.linearityModulus k = 2 * k
    ∧ cubePlusSquareIsDifferentiable.linearityModulus k = 3 * k :=
  ⟨affineIsDifferentiable_modulus a b k,
   squarePlusIdIsDifferentiable_modulus k,
   cubePlusSquareIsDifferentiable_modulus k⟩

end E213.Research.Real213.CutSum
