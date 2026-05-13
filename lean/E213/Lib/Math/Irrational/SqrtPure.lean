import E213.Lib.Math.ModArith.PureNatMod3
import E213.Lib.Math.ModArith.PureNatMod5
import E213.Lib.Math.NatHelpers.PureNat

/-!
# Irrational.SqrtPure — √p irrationality, truly axiom-free (p ∈ {2, 3, 5})

`Sqrt{p}IrrationalPure` for p ∈ {2, 3, 5}: zero-axiom proof of
√p irrationality via infinite descent on squaring map mod p.

Pattern (same template for each prime):
  1. Assume √p = a/b in lowest terms
  2. p divides b² (from b² = p · k² some k)
  3. p divides b (by squaring map analysis mod p)
  4. p divides a (similarly)
  5. a, b both divisible by p — contradicts "lowest terms"

Per-prime namespaces preserved (`Sqrt{p}Pure`).
-/

namespace E213.Lib.Math.Irrational.Sqrt2Pure

open E213.Lib.Math.NatHelpers.PureNat

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

end E213.Lib.Math.Irrational.Sqrt2Pure

namespace E213.Lib.Math.Irrational.Sqrt3Pure

open E213.Lib.Math.NatHelpers.PureNat
open E213.Lib.Math.ModArith.PureNatMod3

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

end E213.Lib.Math.Irrational.Sqrt3Pure

namespace E213.Lib.Math.Irrational.Sqrt5Pure

open E213.Lib.Math.NatHelpers.PureNat
open E213.Lib.Math.ModArith.PureNatMod5

theorem m_mod5_zero_of_sq (m k : Nat) (heq : m * m = 5 * (k * k)) :
    mod5 m = 0 := by
  apply mod5_self_mul_zero
  rw [heq]; exact mod5_five_mul (k * k)

theorem five_split (m : Nat) (h : mod5 m = 0) : ∃ m', m = 5 * m' := by
  rcases nat_quintichotomy m with h' | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact h'
  · exfalso; rw [hk, mod5_five_mul_one] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_two] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_three] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_four] at h; exact Nat.noConfusion h

theorem descent_step (m k : Nat) (heq : m * m = 5 * (k * k))
    (m' : Nat) (hm : m = 5 * m') :
    5 * (m' * m') = k * k := by
  rw [hm, five_mul_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) heq

private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)

theorem sqrt5_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 5 * (k * k) → k = 0 := by
  intro s
  induction s with
  | zero => intro k _ hkn _; exact Nat.le_zero.mp hkn
  | succ n ih =>
      intro k m hkn heq
      by_cases hk : k = 0
      · exact hk
      · exfalso
        have hk_pos : k ≥ 1 := ne_zero_imp_ge_one k hk
        obtain ⟨m', hm_eq⟩ := five_split m (m_mod5_zero_of_sq m k heq)
        have h2 : 5 * (m' * m') = k * k := descent_step m k heq m' hm_eq
        obtain ⟨k', hk_eq⟩ := five_split k (m_mod5_zero_of_sq k m' h2.symm)
        have h3 : m' * m' = 5 * (k' * k') := by
          rw [hk_eq, five_mul_sq] at h2
          exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) h2
        by_cases hk'_zero : k' = 0
        · exact hk (by rw [hk_eq, hk'_zero, Nat.mul_zero])
        · have hk'_pos : k' ≥ 1 := ne_zero_imp_ge_one k' hk'_zero
          have hbnd : 5 * k' ≤ n + 1 := by rw [← hk_eq]; exact hkn
          have hk'_le : k' ≤ n := by
            have h_5k : 5 * k' = k' + (k' + (k' + (k' + k'))) := by
              rw [show (5 : Nat) = 1 + 1 + 1 + 1 + 1 from rfl,
                  add_mul, add_mul, add_mul, add_mul, Nat.one_mul,
                  Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
            rw [h_5k] at hbnd
            have h_step : k' + 1 ≤ k' + (k' + (k' + (k' + k'))) := by
              apply Nat.add_le_add_left
              exact Nat.le_trans hk'_pos
                (Nat.le_add_right k' (k' + (k' + k')))
            exact Nat.le_of_succ_le_succ (Nat.le_trans h_step hbnd)
          exact hk'_zero (ih k' m' hk'_le h3)

/-- **√5 irrationality, truly axiom-free**. -/
theorem sqrt5_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 5 * (k * k) := by
  intro heq
  have h := sqrt5_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Lib.Math.Irrational.Sqrt5Pure
