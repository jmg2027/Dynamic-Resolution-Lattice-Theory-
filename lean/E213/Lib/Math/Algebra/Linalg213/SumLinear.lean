import E213.Lib.Math.Algebra.Linalg213.Permutation
import E213.Meta.Int213.PolyIntM
import E213.Meta.Tactic.List213

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
open E213.Tactic.List213 (map_congr)

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

/-- `Σₓ 0 = 0` over any list. -/
theorem sumZ_map_zero {α : Type} : ∀ (L : List α), sumZ (L.map (fun _ => (0 : Int))) = 0
  | [] => rfl
  | x :: xs => by
    show (0 : Int) + sumZ (xs.map (fun _ => (0 : Int))) = 0
    rw [sumZ_map_zero xs]; rfl

/-- **Finite Fubini.**  `Σₓ Σᵧ f x y = Σᵧ Σₓ f x y` over two lists (`sumZ` double sum swap).
    Induction on `L` via `sumZ_map_add` (cons distributes the inner sum over `M`). -/
theorem sumZ_swap {α β : Type} (f : α → β → Int) :
    ∀ (L : List α) (M : List β),
      sumZ (L.map (fun x => sumZ (M.map (fun y => f x y))))
        = sumZ (M.map (fun y => sumZ (L.map (fun x => f x y))))
  | [], M => by
    show (0 : Int) = sumZ (M.map (fun y => sumZ (([] : List α).map (fun x => f x y))))
    rw [show M.map (fun y => sumZ (([] : List α).map (fun x => f x y)))
          = M.map (fun _ => (0 : Int)) from map_congr (fun y _ => rfl), sumZ_map_zero]
  | x :: xs, M => by
    show sumZ (M.map (fun y => f x y))
          + sumZ (xs.map (fun x => sumZ (M.map (fun y => f x y))))
       = sumZ (M.map (fun y => f x y + sumZ (xs.map (fun x => f x y))))
    rw [sumZ_map_add (fun y => f x y) (fun y => sumZ (xs.map (fun x => f x y))) M,
        sumZ_swap f xs M]

end E213.Lib.Math.Algebra.Linalg213.SumLinear
