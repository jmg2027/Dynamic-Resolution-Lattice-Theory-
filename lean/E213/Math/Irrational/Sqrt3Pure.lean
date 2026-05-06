import E213.Math.ModArith.PureNatMod3

/-!
# Sqrt3IrrationalPure: √3 irrationality, **truly axiom-free**

Generalization of `Sqrt2IrrationalPure` to p = 3.  Same descent pattern —
squaring map analysis of prime-modular structure + infinite descent.

Uses Lean as a *pure type checker* only.

## Significance

Advance of the method — generalization of sqrt2: sqrt p is irrational
for any prime p, descent via mod-p.  Concrete instance for p = 3.
-/

namespace E213.Math.Irrational.Sqrt3Pure

open E213.Math.PureNat
open E213.Math.ModArith.PureNatMod3

/-- m^2 = 3*(k*k) → mod3 m = 0. -/
theorem m_mod3_zero_of_sq (m k : Nat) (heq : m * m = 3 * (k * k)) :
    mod3 m = 0 := by
  apply mod3_self_mul_zero
  rw [heq]
  exact mod3_three_mul (k * k)

/-- mod3 m = 0 → ∃ m', m = 3 * m'. -/
theorem three_split (m : Nat) (h : mod3 m = 0) : ∃ m', m = 3 * m' := by
  cases nat_trichotomy m with
  | inl h' => exact h'
  | inr h' =>
      cases h' with
      | inl h'' =>
          obtain ⟨k, hk⟩ := h''
          exfalso; rw [hk, mod3_three_mul_one] at h
          exact Nat.noConfusion h
      | inr h'' =>
          obtain ⟨k, hk⟩ := h''
          exfalso; rw [hk, mod3_three_mul_two] at h
          exact Nat.noConfusion h

/-- Descent step: m = 3*m', m^2 = 3*(k*k) → 3*(m'*m') = k*k. -/
theorem descent_step (m k : Nat) (heq : m * m = 3 * (k * k))
    (m' : Nat) (hm : m = 3 * m') :
    3 * (m' * m') = k * k := by
  rw [hm] at heq
  rw [three_mul_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) heq

private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)

theorem sqrt3_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 3 * (k * k) → k = 0 := by
  intro s
  induction s with
  | zero =>
      intro k _ hkn _
      exact Nat.le_zero.mp hkn
  | succ n ih =>
      intro k m hkn heq
      by_cases hk : k = 0
      · exact hk
      · exfalso
        have hk_pos : k ≥ 1 := ne_zero_imp_ge_one k hk
        have hm_mod := m_mod3_zero_of_sq m k heq
        obtain ⟨m', hm_eq⟩ := three_split m hm_mod
        have h2 : 3 * (m' * m') = k * k := descent_step m k heq m' hm_eq
        have hk_mod := m_mod3_zero_of_sq k m' h2.symm
        obtain ⟨k', hk_eq⟩ := three_split k hk_mod
        have h3 : m' * m' = 3 * (k' * k') := by
          rw [hk_eq] at h2
          rw [three_mul_sq] at h2
          exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h2
        by_cases hk'_zero : k' = 0
        · apply hk
          rw [hk_eq, hk'_zero, Nat.mul_zero]
        · have hk'_pos : k' ≥ 1 := ne_zero_imp_ge_one k' hk'_zero
          have hbnd : 3 * k' ≤ n + 1 := by rw [← hk_eq]; exact hkn
          have hk'_le : k' ≤ n := by
            -- 3*k' ≤ n+1, k' ≥ 1 → k' ≤ n.
            -- 3*k' = k' + (2*k') ≥ k' + 2 ≥ k' + 1.
            -- So k' + 1 ≤ 3*k' ≤ n + 1, hence k' ≤ n.
            have h_3k : 3 * k' = k' + (k' + k') := by
              rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
                  add_mul, add_mul, Nat.one_mul, Nat.add_assoc]
            rw [h_3k] at hbnd
            have h_step : k' + 1 ≤ k' + (k' + k') := by
              apply Nat.add_le_add_left
              exact Nat.le_trans hk'_pos (Nat.le_add_right k' k')
            exact Nat.le_of_succ_le_succ (Nat.le_trans h_step hbnd)
          exact hk'_zero (ih k' m' hk'_le h3)

/-- **√3 irrationality, truly axiom-free**. -/
theorem sqrt3_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 3 * (k * k) := by
  intro heq
  have h := sqrt3_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Math.Irrational.Sqrt3Pure
