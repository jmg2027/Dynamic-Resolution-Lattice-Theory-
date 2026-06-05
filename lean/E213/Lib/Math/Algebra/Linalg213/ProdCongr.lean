import E213.Lib.Math.Algebra.Linalg213.ProdLperm
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Meta.Int213.Order

/-!
# Linalg213 — `prodZ` congruence and factoring (mapped form)

Reusable `prodZ` infrastructure for product arguments mod `p` (Gauss's lemma, Wilson):

  * `prodZ_congr_map` — elementwise `P ∣ (g x − h x)` ⟹ `P ∣ (∏ g − ∏ h)` (telescoping).
  * `prodZ_map_mul` — `∏ (g·h) = (∏ g)·(∏ h)`.
  * `prodZ_map_const_mul` — `∏ (c·g) = c^(len) · ∏ g`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.ProdCongr

open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ)
open E213.Lib.Math.NumberTheory.PolyRoot (dvd_add' dvd_mul_left')
open E213.Meta.Int213.Order (sub_self_zero)
open E213.Meta.Int213.PolyIntM (mul_zeroZ)

/-- **Product congruence (mapped).**  If `P ∣ (g x − h x)` for every `x ∈ L`, then
    `P ∣ (∏ₓ g x − ∏ₓ h x)`.  Telescope `g·B − h·H = g·(B−H) + H·(g−h)`. -/
theorem prodZ_congr_map {α : Type} (P : Int) (g h : α → Int) :
    ∀ (L : List α), (∀ x ∈ L, P ∣ (g x - h x)) →
      P ∣ (prodZ (L.map g) - prodZ (L.map h))
  | [], _ => by show P ∣ ((1 : Int) - 1); rw [sub_self_zero]; exact ⟨0, (mul_zeroZ P).symm⟩
  | x :: xs, hc => by
    show P ∣ (g x * prodZ (xs.map g) - h x * prodZ (xs.map h))
    have ih : P ∣ (prodZ (xs.map g) - prodZ (xs.map h)) :=
      prodZ_congr_map P g h xs (fun y hy => hc y (List.Mem.tail x hy))
    have hx : P ∣ (g x - h x) := hc x (List.Mem.head xs)
    have hid : g x * prodZ (xs.map g) - h x * prodZ (xs.map h)
             = g x * (prodZ (xs.map g) - prodZ (xs.map h))
               + prodZ (xs.map h) * (g x - h x) := by ring_intZ
    rw [hid]
    exact dvd_add' (dvd_mul_left' ih (g x)) (dvd_mul_left' hx (prodZ (xs.map h)))

/-- `∏ₓ (g x · h x) = (∏ₓ g x) · (∏ₓ h x)`. -/
theorem prodZ_map_mul {α : Type} (g h : α → Int) :
    ∀ (L : List α), prodZ (L.map (fun x => g x * h x)) = prodZ (L.map g) * prodZ (L.map h)
  | [] => by show (1 : Int) = 1 * 1; rw [Int.one_mul]
  | x :: xs => by
    show g x * h x * prodZ (xs.map (fun y => g y * h y))
       = g x * prodZ (xs.map g) * (h x * prodZ (xs.map h))
    rw [prodZ_map_mul g h xs]; ring_intZ

/-- `∏ₓ (c · g x) = c^(len L) · ∏ₓ g x`. -/
theorem prodZ_map_const_mul {α : Type} (c : Int) (g : α → Int) :
    ∀ (L : List α), prodZ (L.map (fun x => c * g x)) = c ^ L.length * prodZ (L.map g)
  | [] => by show (1 : Int) = c ^ 0 * 1; rw [Int.pow_zero, Int.one_mul]
  | x :: xs => by
    show c * g x * prodZ (xs.map (fun y => c * g y))
       = c ^ (xs.length + 1) * (g x * prodZ (xs.map g))
    rw [prodZ_map_const_mul c g xs, Int.pow_succ]; ring_intZ

end E213.Lib.Math.Algebra.Linalg213.ProdCongr
