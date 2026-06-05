import E213.Lib.Math.Algebra.Linalg213.Permutation
import E213.Meta.Int213.PolyIntM

/-!
# Linalg213 — `sumZ` linearity (mapped form)

The additive analog of `ProdCongr`: `sumZ` distributes over a pointwise sum and pulls out a constant
factor.  Reusable for the floor-sum arguments toward quadratic reciprocity.

  * `sumZ_map_add` — `Σ (g + h) = Σ g + Σ h`.
  * `sumZ_map_const_mul` — `Σ (c · g) = c · Σ g`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.SumLinear

open E213.Lib.Math.Algebra.Linalg213.Permutation (sumZ)
open E213.Meta.Int213.PolyIntM (mul_zeroZ)

/-- `Σₓ (g x + h x) = (Σₓ g x) + (Σₓ h x)`. -/
theorem sumZ_map_add {α : Type} (g h : α → Int) :
    ∀ (L : List α), sumZ (L.map (fun x => g x + h x)) = sumZ (L.map g) + sumZ (L.map h)
  | [] => rfl
  | x :: xs => by
    show (g x + h x) + sumZ (xs.map (fun y => g y + h y))
       = (g x + sumZ (xs.map g)) + (h x + sumZ (xs.map h))
    rw [sumZ_map_add g h xs]; ring_intZ

/-- `Σₓ (g x − h x) = (Σₓ g x) − (Σₓ h x)`. -/
theorem sumZ_map_sub {α : Type} (g h : α → Int) :
    ∀ (L : List α), sumZ (L.map (fun x => g x - h x)) = sumZ (L.map g) - sumZ (L.map h)
  | [] => rfl
  | x :: xs => by
    show (g x - h x) + sumZ (xs.map (fun y => g y - h y))
       = (g x + sumZ (xs.map g)) - (h x + sumZ (xs.map h))
    rw [sumZ_map_sub g h xs]; ring_intZ

/-- `Σₓ (c · g x) = c · Σₓ g x`. -/
theorem sumZ_map_const_mul {α : Type} (c : Int) (g : α → Int) :
    ∀ (L : List α), sumZ (L.map (fun x => c * g x)) = c * sumZ (L.map g)
  | [] => by show (0 : Int) = c * 0; exact (mul_zeroZ c).symm
  | x :: xs => by
    show c * g x + sumZ (xs.map (fun y => c * g y)) = c * (g x + sumZ (xs.map g))
    rw [sumZ_map_const_mul c g xs]; ring_intZ

end E213.Lib.Math.Algebra.Linalg213.SumLinear
