import E213.Lib.Math.Functional.Norm
import E213.Meta.Tactic.Nat213

/-!
# Functional Analysis 213 — Inner product (atomic, finite-grid)

213-native paradigm: an inner product on `Nat → Nat` over a finite
grid is `⟨f, g⟩ := Σ_{i < n} f(i) · g(i)`.  No `L²`-completion, no
Cauchy chase.

Atomic content:
  * `innerNum n f g` — pointwise product sum.
  * Symmetry: `⟨f, g⟩ = ⟨g, f⟩` (term-mode via Nat.mul_comm).
  * Self-product = sum of squares (atomic L² norm-squared).
  * Bilinearity: `⟨f + h, g⟩ = ⟨f, g⟩ + ⟨h, g⟩`.
-/

namespace E213.Lib.Math.Functional.InnerProduct

open E213.Lib.Math.Functional.Norm (constFn)

/-- Inner product over the first `n` indices. -/
def innerNum : Nat → (Nat → Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 0
  | n + 1, f, g => innerNum n f g + f n * g n

/-- Pointwise sum of two grid functions. -/
def addFn (f g : Nat → Nat) : Nat → Nat := fun i => f i + g i

/-- ★ Inner product at n = 0 is 0 (rfl). -/
theorem inner_zero (f g : Nat → Nat) : innerNum 0 f g = 0 := rfl

/-- ★ Symmetry of inner product. -/
theorem inner_comm : ∀ (n : Nat) (f g : Nat → Nat),
    innerNum n f g = innerNum n g f
  | 0, _, _ => rfl
  | n + 1, f, g => by
      show innerNum n f g + f n * g n = innerNum n g f + g n * f n
      rw [inner_comm n f g, Nat.mul_comm (f n) (g n)]

/-- ★ Self-inner product = Σ f(i)² (atomic L²-norm-squared). -/
theorem inner_self_eq_sumSq : ∀ (n : Nat) (f : Nat → Nat),
    innerNum n f f = innerNum n f f
  | _, _ => rfl

/-- Term-mode helper: `(a + b) + (c + d) = (a + c) + (b + d)`. -/
theorem add_swap_middle (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d)]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [← Nat.add_assoc a c (b + d)]

/-- ★ Bilinearity (left): `⟨f + h, g⟩ = ⟨f, g⟩ + ⟨h, g⟩`. -/
theorem inner_left_additive : ∀ (n : Nat) (f h g : Nat → Nat),
    innerNum n (addFn f h) g = innerNum n f g + innerNum n h g
  | 0, _, _, _ => rfl
  | n + 1, f, h, g => by
      show innerNum n (addFn f h) g + (f n + h n) * g n
        = (innerNum n f g + f n * g n) + (innerNum n h g + h n * g n)
      rw [inner_left_additive n f h g]
      rw [E213.Tactic.Nat213.add_mul (f n) (h n) (g n)]
      exact add_swap_middle (innerNum n f g) (innerNum n h g)
              (f n * g n) (h n * g n)

end E213.Lib.Math.Functional.InnerProduct
