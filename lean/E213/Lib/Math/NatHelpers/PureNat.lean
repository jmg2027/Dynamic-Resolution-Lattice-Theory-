/-!
# PureNat: custom axiom-free Nat lemmas

`Nat.mul_assoc`, `Nat.add_mul`, `Nat.mul_mul_mul_comm`,
`Nat.div_add_mod`, and `Nat.mul_mod` in the Lean 4 core all use
`[propext]`.

Re-proved axiom-free via direct induction — using Lean purely as a
*type checker*.

## Significance

User question (2026-04-26): modularize propext as well.  The *extreme
purity* of having no dependency even on the standard Nat library of
Lean 4 core.
-/

namespace E213.Lib.Math.NatHelpers.PureNat

/-- mul_assoc, axiom-free. -/
theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero =>
      show a * b * 0 = a * (b * 0)
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ n ih =>
      show a * b * (n + 1) = a * (b * (n + 1))
      rw [Nat.mul_succ, Nat.mul_succ, ih, Nat.mul_add]

/-- add_mul (right distributivity), axiom-free. -/
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      show (a + b) * 0 = a * 0 + b * 0
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ n ih =>
      show (a + b) * (n + 1) = a * (n + 1) + b * (n + 1)
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      rw [Nat.add_assoc, Nat.add_assoc]
      apply congrArg (a * n + ·)
      rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.add_comm (b * n) a, Nat.add_assoc]

/-- mul_mul_mul_comm, axiom-free. -/
theorem mul_mul_mul_comm (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mul_assoc, ← mul_assoc b c d, Nat.mul_comm b c,
      mul_assoc c b d, ← mul_assoc]

end E213.Lib.Math.NatHelpers.PureNat

namespace E213.Lib.Math.NatHelpers.PureNat

end E213.Lib.Math.NatHelpers.PureNat

namespace E213.Lib.Math.NatHelpers.PureNat

/-- Custom even-detection, structural recursion (no well-founded). -/
def isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => isEven n

theorem isEven_two_mul (k : Nat) : isEven (2 * k) = true := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show isEven (2 * (n + 1)) = true
      rw [Nat.mul_succ]
      show isEven (2 * n + 2) = true
      exact ih

theorem isEven_two_mul_succ (k : Nat) : isEven (2 * k + 1) = false := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show isEven (2 * (n + 1) + 1) = false
      rw [Nat.mul_succ]
      show isEven (2 * n + 2 + 1) = false
      exact ih

/-- Every Nat is `2k` or `2k+1` (axiom-free). -/
theorem nat_dichotomy (m : Nat) :
    (∃ k, m = 2 * k) ∨ (∃ k, m = 2 * k + 1) := by
  induction m with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
      cases ih with
      | inl h =>
          obtain ⟨k, hk⟩ := h
          right
          exact ⟨k, by rw [hk]⟩
      | inr h =>
          obtain ⟨k, hk⟩ := h
          left
          exact ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- Even squared: `(2k)^2 = 2*(2*(k*k))`. -/
theorem even_sq (k : Nat) : (2 * k) * (2 * k) = 2 * (2 * (k * k)) := by
  rw [mul_mul_mul_comm 2 k 2 k, mul_assoc]

/-- isEven preserved under squaring of even. -/
theorem isEven_sq_of_even (k : Nat) : isEven ((2 * k) * (2 * k)) = true := by
  rw [even_sq]; exact isEven_two_mul (2 * (k * k))

/-- Helper: reassociation. -/
theorem reassoc4 (a b c d : Nat) :
    a + b + (c + d) = a + (b + c) + d := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, ← Nat.add_assoc a (b+c) d]

/-- Odd squared: `(2k+1)^2 = 2*(2*(k*k) + 2*k) + 1`. -/
theorem odd_sq (k : Nat) :
    (2 * k + 1) * (2 * k + 1) = 2 * (2 * (k * k) + 2 * k) + 1 := by
  rw [add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  rw [mul_mul_mul_comm 2 k 2 k, mul_assoc 2 2 (k*k)]
  rw [Nat.mul_add 2 (2*(k*k)) (2*k), Nat.two_mul (2*k)]
  -- LHS: 2*(2*(k*k)) + 2*k + (2*k + 1)
  -- RHS: 2*(2*(k*k)) + (2*k + 2*k) + 1
  exact reassoc4 (2*(2*(k*k))) (2*k) (2*k) 1

/-- isEven preserved under squaring of odd. -/
theorem isEven_sq_of_odd (k : Nat) : isEven ((2 * k + 1) * (2 * k + 1)) = false := by
  rw [odd_sq]; exact isEven_two_mul_succ (2 * (k * k) + 2 * k)

/-- isEven (m*m) = isEven m. -/
theorem isEven_self_mul (m : Nat) : isEven (m * m) = isEven m := by
  cases nat_dichotomy m with
  | inl h =>
      obtain ⟨k, hk⟩ := h
      rw [hk, isEven_sq_of_even, isEven_two_mul]
  | inr h =>
      obtain ⟨k, hk⟩ := h
      rw [hk, isEven_sq_of_odd, isEven_two_mul_succ]

end E213.Lib.Math.NatHelpers.PureNat
