import E213.Research.Real213.DifferentiableInstances

/-!
# Research.Real213DifferentiableHigherPow

Phase AF: IsDifferentiable polynomial coverage to degrees 5-8
(parity with quinticIsSmooth..octicIsSmooth chain).
-/

namespace E213.Research.Real213.DifferentiableHigherPow

open E213.Firmware E213.Hypervisor

/-- x ↦ x⁵ = x² · x³. -/
def quinticIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) :=
  mulIsDifferentiable squareIsDifferentiable cubeIsDifferentiable

/-- x ↦ x⁶ = x³ · x³. -/
def sexticIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x (cutMul x x))
                                      (cutMul x (cutMul x x))) :=
  mulIsDifferentiable cubeIsDifferentiable cubeIsDifferentiable

/-- x ↦ x⁷ = x³ · x⁴. -/
def septicIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x (cutMul x x))
                                      (cutMul (cutMul x x) (cutMul x x))) :=
  mulIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable

/-- x ↦ x⁸ = x⁴ · x⁴. -/
def octicIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                      (cutMul (cutMul x x) (cutMul x x))) :=
  mulIsDifferentiable quarticIsDifferentiable quarticIsDifferentiable

/-- Quintic modulus: 5k. -/
theorem quinticIsDifferentiable_modulus (k : Nat) :
    quinticIsDifferentiable.linearityModulus k = 5 * k := by
  show squareIsDifferentiable.linearityModulus k
       + cubeIsDifferentiable.linearityModulus k = 5 * k
  rw [squareIsDifferentiable_modulus, cubeIsDifferentiable_modulus]; omega

/-- Sextic modulus: 6k. -/
theorem sexticIsDifferentiable_modulus (k : Nat) :
    sexticIsDifferentiable.linearityModulus k = 6 * k := by
  show cubeIsDifferentiable.linearityModulus k
       + cubeIsDifferentiable.linearityModulus k = 6 * k
  rw [cubeIsDifferentiable_modulus]; omega

/-- Septic modulus: 7k. -/
theorem septicIsDifferentiable_modulus (k : Nat) :
    septicIsDifferentiable.linearityModulus k = 7 * k := by
  show cubeIsDifferentiable.linearityModulus k
       + quarticIsDifferentiable.linearityModulus k = 7 * k
  rw [cubeIsDifferentiable_modulus, quarticIsDifferentiable_modulus]; omega

/-- Octic modulus: 8k. -/
theorem octicIsDifferentiable_modulus (k : Nat) :
    octicIsDifferentiable.linearityModulus k = 8 * k := by
  show quarticIsDifferentiable.linearityModulus k
       + quarticIsDifferentiable.linearityModulus k = 8 * k
  rw [quarticIsDifferentiable_modulus]; omega

/-- Phase AF capstone: degrees 5-8 modulus equalities. -/
theorem polynomial_higher_pow_capstone (k : Nat) :
    quinticIsDifferentiable.linearityModulus k = 5 * k
    ∧ sexticIsDifferentiable.linearityModulus k = 6 * k
    ∧ septicIsDifferentiable.linearityModulus k = 7 * k
    ∧ octicIsDifferentiable.linearityModulus k = 8 * k :=
  ⟨quinticIsDifferentiable_modulus k, sexticIsDifferentiable_modulus k,
   septicIsDifferentiable_modulus k, octicIsDifferentiable_modulus k⟩

end E213.Research.Real213.DifferentiableHigherPow
