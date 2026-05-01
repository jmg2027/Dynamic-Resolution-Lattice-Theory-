/-!
# Research.Sqrt2IrrationalKernelFree: omega-free √2 irrationality

axiom-free version of `Sqrt2Irrational`: without `omega` (which uses
`[propext, Quot.sound]`), so the resulting axiom is ≤ `[propext]`.

## Significance

User question (2026-04-26): Can `propext` + `Quot.sound` in the Lean kernel
also be modularized?  omega is a tactic that uses both `[propext, Quot.sound]`
from baseline Lean 4 core.  Removing omega via manual Nat arithmetic
→ removes Quot.sound from the axiom budget.

`mul_self_mod_two` + `descent_step` + `m_even_of_sq` all use propext only.
One level above the pure type-checker realm (propext is an essential axiom
of Lean 4 core — Prop equality).
-/

namespace E213.Math.Irrational.Sqrt2KernelFree

/-- `m * m % 2 = m % 2`. Pure mod-2 case analysis. -/
theorem mul_self_mod_two (m : Nat) : m * m % 2 = m % 2 := by
  rw [Nat.mul_mod m m 2]
  have hlt : m % 2 < 2 := Nat.mod_lt m (by decide)
  match h : m % 2, hlt with
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, hlt =>
      exfalso
      have h1 : n + 2 ≤ 1 := Nat.le_of_succ_le_succ hlt
      have h2 : n + 1 ≤ 0 := Nat.le_of_succ_le_succ h1
      exact Nat.not_succ_le_zero n h2

end E213.Math.Irrational.Sqrt2KernelFree

namespace E213.Math.Irrational.Sqrt2KernelFree

/-- m * m = 2 * (k * k) → m even. -/
theorem m_even_of_sq (m k : Nat) (heq : m * m = 2 * (k * k)) :
    m % 2 = 0 := by
  have h1 : m * m % 2 = m % 2 := mul_self_mod_two m
  rw [heq] at h1
  rw [Nat.mul_mod_right] at h1
  exact h1.symm

/-- Descent: m even → 2 * m'² = k² when m * m = 2 * k². -/
theorem descent_step (m k : Nat) (heq : m * m = 2 * (k * k))
    (m' : Nat) (hm : m = 2 * m') :
    2 * (m' * m') = k * k := by
  rw [hm] at heq
  have h_assoc : (2 * m') * (2 * m') = 2 * (2 * (m' * m')) := by
    rw [Nat.mul_mul_mul_comm 2 m' 2 m', Nat.mul_assoc]
  rw [h_assoc] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq

end E213.Math.Irrational.Sqrt2KernelFree

namespace E213.Math.Irrational.Sqrt2KernelFree

/-- m even → ∃ m', m = 2 * m'.  Uses Nat.div_add_mod. -/
private theorem even_split (m : Nat) (h : m % 2 = 0) :
    ∃ m', m = 2 * m' := by
  refine ⟨m / 2, ?_⟩
  have hd := Nat.div_add_mod m 2
  rw [h, Nat.add_zero] at hd
  exact hd.symm

/-- k ≠ 0 → k ≥ 1. -/
private theorem ne_zero_imp_ge_one (k : Nat) (h : k ≠ 0) : k ≥ 1 := by
  match k with
  | 0 => exact absurd rfl h
  | n + 1 => exact Nat.succ_le_succ (Nat.zero_le n)

/-- k = 2 * k' implies k' < k+1 (for the descent bound). -/
private theorem half_lt_succ (k' n : Nat) (hbnd : 2 * k' ≤ n + 1)
    (hk_pos : k' ≥ 1) : k' ≤ n := by
  -- 2 * k' ≥ 2  (since k' ≥ 1), so n + 1 ≥ 2, hence n ≥ 1.
  -- 2 * k' ≤ n + 1 means k' + k' ≤ n + 1, hence k' ≤ n + 1 - k' ≤ n (since k' ≥ 1).
  have h1 : 2 * k' = k' + k' := Nat.two_mul k'
  rw [h1] at hbnd
  -- hbnd : k' + k' ≤ n + 1
  -- Want: k' ≤ n.  i.e., k' + 1 ≤ n + 1.  k' + 1 ≤ k' + k' (since k' ≥ 1).
  have h2 : k' + 1 ≤ k' + k' := Nat.add_le_add_left hk_pos k'
  exact Nat.le_of_succ_le_succ (Nat.le_trans h2 hbnd)

end E213.Math.Irrational.Sqrt2KernelFree

namespace E213.Math.Irrational.Sqrt2KernelFree

/-- **Bounded descent**: ∀ s, k ≤ s, m * m = 2 * (k * k) → k = 0.
    No omega — manual Nat arithmetic. -/
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
        -- m even
        have hm_even : m % 2 = 0 := m_even_of_sq m k heq
        obtain ⟨m', hm_eq⟩ := even_split m hm_even
        have h2 : 2 * (m' * m') = k * k := descent_step m k heq m' hm_eq
        -- k even
        have hk_even : k % 2 = 0 := m_even_of_sq k m' h2.symm
        obtain ⟨k', hk_eq⟩ := even_split k hk_even
        -- m' * m' = 2 * (k' * k')
        have h3 : m' * m' = 2 * (k' * k') := by
          rw [hk_eq] at h2
          have h_assoc : (2 * k') * (2 * k') = 2 * (2 * (k' * k')) := by
            rw [Nat.mul_mul_mul_comm 2 k' 2 k', Nat.mul_assoc]
          rw [h_assoc] at h2
          exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
        -- 2 case: k' = 0 → k = 0 contradiction; k' ≥ 1 → IH
        by_cases hk'_zero : k' = 0
        · apply hk
          rw [hk_eq, hk'_zero, Nat.mul_zero]
        · have hk'_pos : k' ≥ 1 := ne_zero_imp_ge_one k' hk'_zero
          have hbnd : 2 * k' ≤ n + 1 := by rw [← hk_eq]; exact hkn
          have hk'_le : k' ≤ n := half_lt_succ k' n hbnd hk'_pos
          exact hk'_zero (ih k' m' hk'_le h3)

end E213.Math.Irrational.Sqrt2KernelFree

namespace E213.Math.Irrational.Sqrt2KernelFree

/-- **√2 irrationality, omega-free**: ∀ k ≥ 1, m, m * m ≠ 2 * (k * k).
    Axiom budget = `[propext]` only (no Quot.sound). -/
theorem sqrt2_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 2 * (k * k) := by
  intro heq
  have h := sqrt2_no_rational_aux k k m (Nat.le_refl _) heq
  -- h : k = 0, but hk : k ≥ 1
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Math.Irrational.Sqrt2KernelFree
