import E213.Math.PureNat

/-!
# Research.PureNatMod3: mod-3 descent infrastructure

Generalization of the `PureNat` mod-2 (isEven) family to p = 3.
Same structural-recursion + Bool/Nat pattern.

## Significance

User directive: advance the method.  The mod-2 descent abstraction can
be lifted to mod-p (general prime) — this module is a mod-3 case
study.  Next step is sqrt3_irrational, then a generic prime-mod descent
template.
-/

namespace E213.Math.ModArith.PureNatMod3

/-- Custom mod-3, structural recursion. -/
def mod3 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => mod3 n

theorem mod3_three_mul (k : Nat) : mod3 (3 * k) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show mod3 (3 * (n + 1)) = 0
      rw [Nat.mul_succ]
      show mod3 (3 * n + 3) = 0
      exact ih

theorem mod3_three_mul_one (k : Nat) : mod3 (3 * k + 1) = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show mod3 (3 * (n + 1) + 1) = 1
      rw [Nat.mul_succ]
      show mod3 (3 * n + 3 + 1) = 1
      exact ih

theorem mod3_three_mul_two (k : Nat) : mod3 (3 * k + 2) = 2 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show mod3 (3 * (n + 1) + 2) = 2
      rw [Nat.mul_succ]
      show mod3 (3 * n + 3 + 2) = 2
      exact ih

/-- Trichotomy: every Nat is 3k, 3k+1, or 3k+2. -/
theorem nat_trichotomy (n : Nat) :
    (∃ k, n = 3 * k) ∨ (∃ k, n = 3 * k + 1) ∨ (∃ k, n = 3 * k + 2) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m ih =>
      cases ih with
      | inl h =>
          obtain ⟨k, hk⟩ := h
          right; left
          exact ⟨k, by rw [hk]⟩
      | inr h =>
          cases h with
          | inl h' =>
              obtain ⟨k, hk⟩ := h'
              right; right
              exact ⟨k, by rw [hk]⟩
          | inr h' =>
              obtain ⟨k, hk⟩ := h'
              left
              exact ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

end E213.Math.ModArith.PureNatMod3

namespace E213.Math.ModArith.PureNatMod3

open E213.Math.PureNat

/-- (3k)^2 = 3*(3*(k*k)). -/
theorem three_mul_sq (k : Nat) :
    (3 * k) * (3 * k) = 3 * (3 * (k * k)) := by
  rw [mul_mul_mul_comm 3 k 3 k, mul_assoc]

/-- (3k+1)^2 = 3*(3*k*k + 2*k) + 1. -/
theorem three_mul_one_sq (k : Nat) :
    (3 * k + 1) * (3 * k + 1) = 3 * (3 * (k * k) + 2 * k) + 1 := by
  rw [add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  rw [mul_mul_mul_comm 3 k 3 k, mul_assoc 3 3 (k*k)]
  rw [Nat.mul_add 3 (3*(k*k)) (2*k)]
  -- LHS: 3*(3*(k*k)) + 3*k + (3*k + 1)
  -- RHS: 3*(3*(k*k)) + 3*(2*k) + 1
  have h1 : 3 * (2 * k) = 3 * k + 3 * k := by
    rw [Nat.two_mul k, Nat.mul_add]
  rw [h1]
  -- goal: A + 3*k + (3*k + 1) = A + (3*k + 3*k) + 1
  exact reassoc4 (3 * (3 * (k * k))) (3*k) (3*k) 1

/-- (3k+2)^2 = 3*(3*k*k + 4*k + 1) + 1. -/
theorem three_mul_two_sq (k : Nat) :
    (3 * k + 2) * (3 * k + 2) = 3 * (3 * (k * k) + 4 * k + 1) + 1 := by
  -- (3k+2)² = 9k² + 12k + 4 = 9k² + 12k + 3 + 1 = 3*(3k²+4k+1) + 1
  rw [add_mul, Nat.mul_add, Nat.mul_add]
  -- (3k)*(3k+2) + 2*(3k+2)
  -- = (3k)*(3k) + (3k)*2 + (2*(3k) + 2*2)
  rw [mul_mul_mul_comm 3 k 3 k, mul_assoc 3 3 (k*k)]
  -- (3k)*(3k) → 3 * (3 * (k*k))
  -- (3k)*2 = 6*k = 3*(2*k)
  rw [show 3 * k * 2 = 3 * (2 * k) from by
    rw [mul_assoc 3 k 2, Nat.mul_comm k 2]]
  -- 2*(3k) = 6k = 3*(2k)
  rw [show 2 * (3 * k) = 3 * (2 * k) from by
    rw [← mul_assoc, Nat.mul_comm 2 3, mul_assoc]]
  -- 2*2 = 4 by rfl
  -- Now: 3*(3*(k*k)) + 3*(2*k) + (3*(2*k) + 4)
  -- Want: 3*(3*(k*k) + 4*k + 1) + 1
  --     = 3*(3*(k*k)) + 3*(4*k) + 3 + 1
  --     = 3*(3*(k*k)) + 12*k + 4
  rw [Nat.mul_add 3 (3*(k*k) + 4*k) 1, Nat.mul_one,
      Nat.mul_add 3 (3*(k*k)) (4*k)]
  -- RHS now: 3*(3*(k*k)) + 3*(4*k) + 3 + 1
  -- LHS: 3*(3*(k*k)) + 3*(2*k) + (3*(2*k) + 2*2)  (2*2 = 4)
  rw [show (2 : Nat) * 2 = 4 from rfl]
  rw [show 3 * (4 * k) = 3 * (2 * k) + 3 * (2 * k) from by
    rw [show (4 : Nat) * k = 2 * k + 2 * k from by
      rw [show (4 : Nat) = 2 + 2 from rfl, add_mul]]
    rw [Nat.mul_add 3 (2*k) (2*k)]]
  rw [show (4 : Nat) = 3 + 1 from rfl, ← Nat.add_assoc]
  -- Goal: A + 3*(2*k) + (3*(2*k) + (3 + 1)) = A + (3*(2*k) + 3*(2*k)) + 3 + 1
  exact reassoc4 (3*(3*(k*k))) (3*(2*k)) (3*(2*k)) 4

/-- Self-multiplication rule for mod3: m² mod 3 = 0 ↔ m mod 3 = 0. -/
theorem mod3_self_mul_zero (m : Nat) :
    mod3 (m * m) = 0 → mod3 m = 0 := by
  intro h
  cases nat_trichotomy m with
  | inl hm => obtain ⟨k, hk⟩ := hm; rw [hk]; exact mod3_three_mul k
  | inr hm =>
      cases hm with
      | inl hm' =>
          obtain ⟨k, hk⟩ := hm'
          exfalso
          rw [hk, three_mul_one_sq, mod3_three_mul_one] at h
          exact Nat.noConfusion h
      | inr hm' =>
          obtain ⟨k, hk⟩ := hm'
          exfalso
          rw [hk, three_mul_two_sq, mod3_three_mul_one] at h
          exact Nat.noConfusion h

end E213.Math.ModArith.PureNatMod3
