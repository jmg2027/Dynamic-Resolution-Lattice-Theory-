import E213.Math.Real213.DifferentiableHigherPow

/-!
# Research.Real213DifferentiableHighOrder

Phase AK: IsDifferentiable selected high-order polynomials.

  nonic     : x⁹  = x⁴·x⁵, modulus = 9k
  decic     : x¹⁰ = x⁵·x⁵, modulus = 10k
  dodecic   : x¹² = x⁴·x⁸, modulus = 12k
  hexadecic : x¹⁶ = x⁸·x⁸, modulus = 16k
-/

namespace E213.Math.Real213.DifferentiableHighOrder

open E213.Firmware E213.Hypervisor

/-- x ↦ x⁹ = x⁴ · x⁵. -/
def nonicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul x x) (cutMul x x))
             (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  mulIsDifferentiable quarticIsDifferentiable quinticIsDifferentiable

/-- x ↦ x¹⁰ = x⁵ · x⁵. -/
def decicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul x x) (cutMul x (cutMul x x)))
             (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  mulIsDifferentiable quinticIsDifferentiable quinticIsDifferentiable

/-- x ↦ x¹² = x⁴ · x⁸. -/
def dodecicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul x x) (cutMul x x))
             (cutMul (cutMul (cutMul x x) (cutMul x x))
                     (cutMul (cutMul x x) (cutMul x x)))) :=
  mulIsDifferentiable quarticIsDifferentiable octicIsDifferentiable

/-- x ↦ x¹⁶ = x⁸ · x⁸. -/
def hexadecicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul (cutMul x x) (cutMul x x))
                     (cutMul (cutMul x x) (cutMul x x)))
             (cutMul (cutMul (cutMul x x) (cutMul x x))
                     (cutMul (cutMul x x) (cutMul x x)))) :=
  mulIsDifferentiable octicIsDifferentiable octicIsDifferentiable

theorem nonicIsDifferentiable_modulus (k : Nat) :
    nonicIsDifferentiable.linearityModulus k = 9 * k := by
  show quarticIsDifferentiable.linearityModulus k
       + quinticIsDifferentiable.linearityModulus k = 9 * k
  rw [quarticIsDifferentiable_modulus, quinticIsDifferentiable_modulus]; omega

theorem decicIsDifferentiable_modulus (k : Nat) :
    decicIsDifferentiable.linearityModulus k = 10 * k := by
  show quinticIsDifferentiable.linearityModulus k
       + quinticIsDifferentiable.linearityModulus k = 10 * k
  rw [quinticIsDifferentiable_modulus]; omega

theorem dodecicIsDifferentiable_modulus (k : Nat) :
    dodecicIsDifferentiable.linearityModulus k = 12 * k := by
  show quarticIsDifferentiable.linearityModulus k
       + octicIsDifferentiable.linearityModulus k = 12 * k
  rw [quarticIsDifferentiable_modulus, octicIsDifferentiable_modulus]; omega

theorem hexadecicIsDifferentiable_modulus (k : Nat) :
    hexadecicIsDifferentiable.linearityModulus k = 16 * k := by
  show octicIsDifferentiable.linearityModulus k
       + octicIsDifferentiable.linearityModulus k = 16 * k
  rw [octicIsDifferentiable_modulus]; omega

theorem polynomial_high_order_capstone (k : Nat) :
    nonicIsDifferentiable.linearityModulus k = 9 * k
    ∧ decicIsDifferentiable.linearityModulus k = 10 * k
    ∧ dodecicIsDifferentiable.linearityModulus k = 12 * k
    ∧ hexadecicIsDifferentiable.linearityModulus k = 16 * k :=
  ⟨nonicIsDifferentiable_modulus k, decicIsDifferentiable_modulus k,
   dodecicIsDifferentiable_modulus k, hexadecicIsDifferentiable_modulus k⟩

end E213.Math.Real213.DifferentiableHighOrder
