import E213.Research.Real213PhaseADCapstone

/-!
# Research.Real213DifferentiableInstances

Phase AE-1: concrete polynomial IsDifferentiable instances mirroring
the IsSmooth instances (`squareIsSmooth`, `cubeIsSmooth`, etc.) plus
their derivative closed forms and modulus equalities.

## Instances

  squareIsDifferentiable    : x ↦ x²,     d/dx = 2x
  cubeIsDifferentiable      : x ↦ x³,     d/dx = 3x²
  quarticIsDifferentiable   : x ↦ x⁴,     d/dx = 4x³

## Modulus

  Each derivative shares the function's linearityModulus = degree × k.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- x ↦ x² = cutMul x x is differentiable; d/dx [x²] follows
    product rule: 1·x + x·1 (≈ 2x). -/
def squareIsDifferentiable : IsDifferentiable (fun x => cutMul x x) :=
  mulIsDifferentiable idIsDifferentiable idIsDifferentiable

/-- x ↦ x³ = cutMul x (cutMul x x) is differentiable. -/
def cubeIsDifferentiable :
    IsDifferentiable (fun x => cutMul x (cutMul x x)) :=
  mulIsDifferentiable idIsDifferentiable squareIsDifferentiable

/-- x ↦ x⁴ = cutMul (x²) (x²) is differentiable. -/
def quarticIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  mulIsDifferentiable squareIsDifferentiable squareIsDifferentiable

/-- Square derivative closed form: 1·x + x·1. -/
theorem square_derivative_form (x : Nat → Nat → Bool) :
    squareIsDifferentiable.derivative x
      = cutSum (cutMul (constCut 1 1) x) (cutMul x (constCut 1 1)) := rfl

/-- Square modulus: linearityModulus k = 2k. -/
theorem squareIsDifferentiable_modulus (k : Nat) :
    squareIsDifferentiable.linearityModulus k = 2 * k := by
  show k + k = 2 * k
  omega

/-- Cube modulus: linearityModulus k = 3k. -/
theorem cubeIsDifferentiable_modulus (k : Nat) :
    cubeIsDifferentiable.linearityModulus k = 3 * k := by
  show k + (k + k) = 3 * k
  omega

/-- Quartic modulus: linearityModulus k = 4k. -/
theorem quarticIsDifferentiable_modulus (k : Nat) :
    quarticIsDifferentiable.linearityModulus k = 4 * k := by
  show (k + k) + (k + k) = 4 * k
  omega

/-- Phase AE-1 capstone: square/cube/quartic moduli. -/
theorem polynomial_differentiable_instances_capstone (k : Nat) :
    squareIsDifferentiable.linearityModulus k = 2 * k
    ∧ cubeIsDifferentiable.linearityModulus k = 3 * k
    ∧ quarticIsDifferentiable.linearityModulus k = 4 * k :=
  ⟨squareIsDifferentiable_modulus k, cubeIsDifferentiable_modulus k,
   quarticIsDifferentiable_modulus k⟩

end E213.Research.Real213CutSum
