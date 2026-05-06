import E213.Math.PureNat

/-!
# Sqrt2IrrationalPure: √2 irrationality, **truly axiom-free**

Removes even propext from `Sqrt2IrrationalKernelFree`.  Uses Lean as
a *pure type checker* only — no axioms whatsoever (propext, Quot.sound,
Classical all absent).

The decisive result of the user question's *ultimate purity*.

## Structure

Direct construction of the sqrt2 irrationality descent on top of
`PureNat`'s axiom-free Nat library.  No omega, no propext-using lemmas.
-/

namespace E213.Math.Irrational.Sqrt2Pure

open E213.Math.PureNat

/-- m^2 = 2*(k*k) → m even. -/
theorem m_even_of_sq (m k : Nat) (heq : m * m = 2 * (k * k)) :
    isEven m = true := by
  have h1 : isEven (m * m) = isEven m := isEven_self_mul m
  rw [heq] at h1
  rw [isEven_two_mul] at h1
  exact h1.symm

/-- isEven m = true → ∃ m', m = 2 * m'. -/
theorem even_split (m : Nat) (h : isEven m = true) : ∃ m', m = 2 * m' := by
  cases nat_dichotomy m with
  | inl h' => exact h'
  | inr h' =>
      obtain ⟨k, hk⟩ := h'
      exfalso
      rw [hk, isEven_two_mul_succ] at h
      exact Bool.noConfusion h

/-- Descent: m = 2*m' and m^2 = 2*(k*k) → 2*(m'*m') = k*k. -/
theorem descent_step (m k : Nat) (heq : m * m = 2 * (k * k))
    (m' : Nat) (hm : m = 2 * m') :
    2 * (m' * m') = k * k := by
  rw [hm] at heq
  rw [even_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq

/-- k ≠ 0 → k ≥ 1. -/
private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)

/-- Bounded descent. -/
theorem sqrt2_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 2 * (k * k) → k = 0 := by
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
        have hm_even := m_even_of_sq m k heq
        obtain ⟨m', hm_eq⟩ := even_split m hm_even
        have h2 : 2 * (m' * m') = k * k := descent_step m k heq m' hm_eq
        have hk_even := m_even_of_sq k m' h2.symm
        obtain ⟨k', hk_eq⟩ := even_split k hk_even
        have h3 : m' * m' = 2 * (k' * k') := by
          rw [hk_eq] at h2
          rw [even_sq] at h2
          exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
        by_cases hk'_zero : k' = 0
        · apply hk
          rw [hk_eq, hk'_zero, Nat.mul_zero]
        · have hk'_pos : k' ≥ 1 := ne_zero_imp_ge_one k' hk'_zero
          have hbnd : 2 * k' ≤ n + 1 := by rw [← hk_eq]; exact hkn
          have hk'_le : k' ≤ n := by
            -- 2 * k' ≤ n + 1 + k'_pos → k' ≤ n
            have h_two : 2 * k' = k' + k' := Nat.two_mul k'
            rw [h_two] at hbnd
            have : k' + 1 ≤ k' + k' := Nat.add_le_add_left hk'_pos k'
            exact Nat.le_of_succ_le_succ (Nat.le_trans this hbnd)
          exact hk'_zero (ih k' m' hk'_le h3)

/-- **√2 irrationality, truly axiom-free**. -/
theorem sqrt2_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 2 * (k * k) := by
  intro heq
  have h := sqrt2_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Math.Irrational.Sqrt2Pure
