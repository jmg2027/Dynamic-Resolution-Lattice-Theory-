import E213.Research.PureNat

/-!
# Research.PureNatMod5: mod-5 descent infrastructure

Generalization of `PureNatMod3` to p = 5.  Same 5-step template
applied — analysis of the squaring kernel of (Z/5)*.

(5k+r)² mod 5:
- r=0: (5k)² = 25k² = 5·(5k²) → 0
- r=1: 25k²+10k+1 = 5·(5k²+2k) + 1 → 1
- r=2: 25k²+20k+4 = 5·(5k²+4k) + 4 → 4
- r=3: 25k²+30k+9 = 5·(5k²+6k+1) + 4 → 4
- r=4: 25k²+40k+16 = 5·(5k²+8k+3) + 1 → 1

Squaring kernel = {0}.  Only 0 squares to 0.
-/

namespace E213.Math.ModArith.PureNatMod5

open E213.Research.PureNat

def mod5 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | n + 5 => mod5 n

theorem mod5_five_mul (k : Nat) : mod5 (5 * k) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show mod5 (5 * (n + 1)) = 0
      rw [Nat.mul_succ]
      show mod5 (5 * n + 5) = 0
      exact ih

theorem mod5_five_mul_one (k : Nat) : mod5 (5 * k + 1) = 1 := by
  induction k with
  | zero => rfl
  | succ n ih => show mod5 (5 * (n + 1) + 1) = 1; rw [Nat.mul_succ]; exact ih

theorem mod5_five_mul_four (k : Nat) : mod5 (5 * k + 4) = 4 := by
  induction k with
  | zero => rfl
  | succ n ih => show mod5 (5 * (n + 1) + 4) = 4; rw [Nat.mul_succ]; exact ih

theorem mod5_five_mul_two (k : Nat) : mod5 (5 * k + 2) = 2 := by
  induction k with
  | zero => rfl
  | succ n ih => show mod5 (5 * (n + 1) + 2) = 2; rw [Nat.mul_succ]; exact ih

theorem mod5_five_mul_three (k : Nat) : mod5 (5 * k + 3) = 3 := by
  induction k with
  | zero => rfl
  | succ n ih => show mod5 (5 * (n + 1) + 3) = 3; rw [Nat.mul_succ]; exact ih

/-- 5-trichotomy: every Nat is 5k, 5k+1, 5k+2, 5k+3, or 5k+4. -/
theorem nat_quintichotomy (n : Nat) :
    (∃ k, n = 5 * k) ∨ (∃ k, n = 5 * k + 1) ∨ (∃ k, n = 5 * k + 2) ∨
    (∃ k, n = 5 * k + 3) ∨ (∃ k, n = 5 * k + 4) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m ih =>
      rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
      · exact Or.inr (Or.inl ⟨k, by rw [hk]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k, by rw [hk]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by rw [hk]⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, by rw [hk]⟩)))
      · exact Or.inl ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- (5k)^2 = 5·(5·k²). -/
theorem five_mul_sq (k : Nat) :
    (5 * k) * (5 * k) = 5 * (5 * (k * k)) := by
  rw [mul_mul_mul_comm 5 k 5 k, mul_assoc]

/-- (5k+1)^2 = 5·(5k²+2k) + 1. -/
theorem five_mul_one_sq (k : Nat) :
    (5 * k + 1) * (5 * k + 1) = 5 * (5 * (k * k) + 2 * k) + 1 := by
  rw [add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  rw [mul_mul_mul_comm 5 k 5 k, mul_assoc 5 5 (k*k)]
  rw [Nat.mul_add 5 (5*(k*k)) (2*k)]
  -- LHS: 5*(5*(k*k)) + 5*k + (5*k + 1)
  -- RHS: 5*(5*(k*k)) + 5*(2*k) + 1
  have h1 : 5 * (2 * k) = 5 * k + 5 * k := by rw [Nat.two_mul k, Nat.mul_add]
  rw [h1]
  exact reassoc4 (5*(5*(k*k))) (5*k) (5*k) 1

/-- General (5k+r)^2 = 5*(5*k^2 + 2*r*k) + r^2 (for r small).
    Use this template for r = 2, 3, 4 cases. -/
theorem five_mul_r_sq (k r : Nat) :
    (5 * k + r) * (5 * k + r) = 5 * (5 * (k * k) + 2 * (r * k)) + r * r := by
  rw [add_mul, Nat.mul_add, Nat.mul_add]
  rw [mul_mul_mul_comm 5 k 5 k, mul_assoc 5 5 (k*k)]
  -- LHS: 5*(5*(k*k)) + 5*k*r + (r*(5*k) + r*r)
  rw [Nat.mul_add 5 (5*(k*k)) (2*(r*k))]
  -- RHS: 5*(5*(k*k)) + 5*(2*(r*k)) + r*r
  -- Need: 5*k*r + (r*(5*k) + r*r) = 5*(2*(r*k)) + r*r
  -- 5*k*r = 5*(r*k) by mul_comm, mul_assoc
  -- r*(5*k) = 5*(r*k) by mul_comm + mul_assoc
  -- Sum = 5*(r*k) + 5*(r*k) = 5*(2*(r*k))
  rw [show 5 * k * r = 5 * (r * k) from by rw [mul_assoc, Nat.mul_comm k r]]
  rw [show r * (5 * k) = 5 * (r * k) from by
    rw [← mul_assoc, Nat.mul_comm r 5, mul_assoc]]
  rw [show 5 * (2 * (r * k)) = 5 * (r * k) + 5 * (r * k) from by
    rw [Nat.two_mul, Nat.mul_add]]
  exact reassoc4 (5*(5*(k*k))) (5*(r*k)) (5*(r*k)) (r*r)

/-- mod5 (5*X + Y) = mod5 Y — generic absorption. -/
theorem mod5_five_mul_add (X Y : Nat) : mod5 (5 * X + Y) = mod5 Y := by
  induction X with
  | zero => rw [Nat.mul_zero, Nat.zero_add]
  | succ n ih =>
      show mod5 (5 * (n + 1) + Y) = mod5 Y
      rw [Nat.mul_succ]
      show mod5 (5 * n + 5 + Y) = mod5 Y
      rw [Nat.add_assoc, Nat.add_comm 5 Y, ← Nat.add_assoc]
      show mod5 (5 * n + Y + 5) = mod5 Y
      -- mod5 (X + 5) = mod5 X by structural recursion
      change mod5 (5 * n + Y) = mod5 Y
      exact ih

/-- m^2 mod 5 = 0 → m mod 5 = 0. -/
theorem mod5_self_mul_zero (m : Nat) :
    mod5 (m * m) = 0 → mod5 m = 0 := by
  intro h
  rcases nat_quintichotomy m with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]; exact mod5_five_mul k
  all_goals (
    exfalso;
    rw [hk, five_mul_r_sq k _, mod5_five_mul_add] at h)
  · -- r = 1, h: mod5 (1*1) = 0
    rw [show (1 : Nat) * 1 = 1 from rfl] at h
    exact Nat.noConfusion h
  · -- r = 2, h: mod5 (2*2) = 0, 2*2 = 4
    rw [show (2 : Nat) * 2 = 4 from rfl] at h
    exact Nat.noConfusion h
  · -- r = 3, h: mod5 (3*3) = 0, 3*3 = 9
    rw [show (3 : Nat) * 3 = 9 from rfl] at h
    exact Nat.noConfusion h
  · -- r = 4, h: mod5 (4*4) = 0, 4*4 = 16
    rw [show (4 : Nat) * 4 = 16 from rfl] at h
    exact Nat.noConfusion h

end E213.Math.ModArith.PureNatMod5
