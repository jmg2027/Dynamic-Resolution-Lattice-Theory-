import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

/-!
# Sqrt2IrrationalKernelFree: ∅-axiom √2 irrationality

Strict ∅-axiom version: replaces every Lean-core `Nat.*` lemma that
brought `propext` (or `[propext, Quot.sound]` via `omega`) with a
213-native term-mode helper.  Per `#print axioms`, every theorem
in this file is `does not depend on any axioms`.

## Eliminated propext sources

  * `Nat.mul_mod`        → `mul_self_mod_two` proved directly
                            via 2-step structural induction
  * `Nat.mul_mod_right`  → `mul2_mod2_local` (∅-axiom)
  * `Nat.mul_mul_mul_comm`,
    `Nat.mul_assoc`      → `mul_assoc_local`,
                            `mul_mul_mul_comm_local` (term-mode)
  * `Nat.div_add_mod`    → `even_split` (∅-axiom via 2-step
                            structural recursion)
  * `omega`              → manual Nat arithmetic (unchanged)

User question: "can `propext` + `Quot.sound` in the
Lean kernel be modularised?"  Answer: yes — `propext` too, when the
content reduces to closed-term `rfl` chains plus structural
recursion on Nat (no well-founded gcd / div termination).
-/

namespace E213.Lib.Math.Irrational.Sqrt2KernelFree

open E213.Meta.Nat.AddMod213

/-! ## Local ∅-axiom helpers -/

/-- `(a * b) * c = a * (b * c)` term-mode.  Lean-core `Nat.mul_assoc`
    brings `propext`. -/
private theorem mul_assoc_local : ∀ (a b c : Nat), (a * b) * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c+1 =>
    let ih : (a * b) * c = a * (b * c) := mul_assoc_local a b c
    let h1 : (a * b) * (c + 1) = (a * b) * c + a * b := Nat.mul_succ (a*b) c
    let h2 : a * (b * (c + 1)) = a * (b * c + b) := congrArg (a * ·) (Nat.mul_succ b c)
    let h3 : a * (b * c + b) = a * (b * c) + a * b := Nat.mul_add a (b*c) b
    h1.trans (ih ▸ (h2.trans h3).symm)

/-- `(a * b) * (c * d) = (a * c) * (b * d)` via `mul_assoc_local`
    + `Nat.mul_comm`.  Replaces Lean-core `Nat.mul_mul_mul_comm`. -/
private theorem mul_mul_mul_comm_local (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mul_assoc_local a b (c*d)]
  rw [← mul_assoc_local b c d]
  rw [Nat.mul_comm b c]
  rw [mul_assoc_local c b d]
  rw [← mul_assoc_local a c (b*d)]

/-- `2 * x % 2 = 0` by structural recursion + `add_mod_gen`. -/
private theorem mul2_mod2_local : ∀ (x : Nat), 2 * x % 2 = 0
  | 0 => rfl
  | x'+1 => by
    show 2 * (x' + 1) % 2 = 0
    rw [Nat.mul_succ, add_mod_gen]
    show (2 * x' % 2 + 0) % 2 = 0
    rw [mul2_mod2_local x']

/-- `(m + 2) % 2 = m % 2` via `add_mod_gen` + `mod_eq_of_lt`. -/
private theorem add2_mod2 (m : Nat) : (m + 2) % 2 = m % 2 := by
  rw [add_mod_gen]
  show (m % 2 + 0) % 2 = m % 2
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt m (by decide))


/-! ## Core square + modular-2 lemmas -/

/-- `(m+2) * (m+2) = m*m + (4*m + 4)` via term-mode rewriting. -/
private theorem expand_sq (m : Nat) : (m + 2) * (m + 2) = m * m + (4 * m + 4) := by
  rw [Nat.mul_add (m+2)]
  rw [Nat.mul_comm (m+2) m]
  rw [Nat.mul_add m m 2]
  rw [Nat.mul_comm (m+2) 2]
  rw [Nat.mul_add 2 m 2]
  rw [Nat.mul_comm m 2]
  rw [Nat.add_assoc (m*m) (2*m) (2*m + 4)]
  rw [← Nat.add_assoc (2*m) (2*m) 4]
  show m * m + (2 * m + 2 * m + 4) = m * m + (4 * m + 4)
  have : 2 * m + 2 * m = 4 * m := by
    rw [Nat.mul_comm 2 m, ← Nat.mul_add m 2 2, Nat.mul_comm m 4]
  rw [this]

/-- `m * m % 2 = m % 2` via 2-step structural induction.  ∅-axiom. -/
theorem mul_self_mod_two : ∀ (m : Nat), m * m % 2 = m % 2
  | 0 => rfl
  | 1 => rfl
  | m+2 => by
    have ih : m * m % 2 = m % 2 := mul_self_mod_two m
    rw [expand_sq, add_mod_gen, ih]
    have h_4m4 : 4 * m + 4 = 2 * (2 * m + 2) := by
      rw [Nat.mul_add 2 (2*m) 2]
      show 4 * m + 4 = 2 * (2*m) + 2*2
      rw [Nat.two_mul (2*m)]
      have : 2 * m + 2 * m = 4 * m := by
        rw [Nat.mul_comm 2 m, ← Nat.mul_add m 2 2, Nat.mul_comm m 4]
      rw [this]
    rw [h_4m4, mul2_mod2_local]
    rw [Nat.add_zero]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt m (by decide))]
    exact (add2_mod2 m).symm


/-! ## Even split + descent step -/

/-- `m * m = 2 * (k * k) → m % 2 = 0`.  ∅-axiom. -/
theorem m_even_of_sq (m k : Nat) (heq : m * m = 2 * (k * k)) :
    m % 2 = 0 := by
  have h1 : m * m % 2 = m % 2 := mul_self_mod_two m
  rw [heq] at h1
  rw [mul2_mod2_local (k * k)] at h1
  exact h1.symm

/-- `m * m = 2 * (k * k)`, `m = 2 * m'` ⟹ `2 * (m' * m') = k * k`.
    Uses `mul_mul_mul_comm_local` + `mul_assoc_local` (∅-axiom). -/
theorem descent_step (m k : Nat) (heq : m * m = 2 * (k * k))
    (m' : Nat) (hm : m = 2 * m') :
    2 * (m' * m') = k * k := by
  rw [hm] at heq
  have h_rearrange : (2 * m') * (2 * m') = 2 * (2 * (m' * m')) := by
    rw [mul_mul_mul_comm_local 2 m' 2 m']
    -- (2 * 2) * (m' * m') = 2 * (2 * (m' * m'))
    rw [mul_assoc_local 2 2 (m' * m')]
  rw [h_rearrange] at heq
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq


/-- `m % 2 = 0 → ∃ m', m = 2 * m'`.  ∅-axiom via 2-step structural
    recursion. -/
private theorem even_split : ∀ (m : Nat), m % 2 = 0 → ∃ m', m = 2 * m'
  | 0, _ => ⟨0, rfl⟩
  | 1, h => absurd h (by decide)
  | m+2, h => by
    have hm2 : (m+2) % 2 = m % 2 := add2_mod2 m
    rw [hm2] at h
    obtain ⟨k, hk⟩ := even_split m h
    exact ⟨k+1, by rw [hk, Nat.mul_succ]⟩

open E213.Tactic.NatHelper renaming one_le_of_ne_zero → ne_zero_imp_ge_one

/-- `2 * k' ≤ n + 1 ∧ k' ≥ 1 → k' ≤ n`. -/
private theorem half_lt_succ (k' n : Nat) (hbnd : 2 * k' ≤ n + 1)
    (hk_pos : k' ≥ 1) : k' ≤ n := by
  have h1 : 2 * k' = k' + k' := Nat.two_mul k'
  rw [h1] at hbnd
  have h2 : k' + 1 ≤ k' + k' := Nat.add_le_add_left hk_pos k'
  exact Nat.le_of_succ_le_succ (Nat.le_trans h2 hbnd)


/-- **Bounded descent**: ∀ s, k ≤ s, m * m = 2 * (k * k) → k = 0.
    Manual Nat arithmetic — no `omega`. -/
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
        have hm_even : m % 2 = 0 := m_even_of_sq m k heq
        obtain ⟨m', hm_eq⟩ := even_split m hm_even
        have h2 : 2 * (m' * m') = k * k := descent_step m k heq m' hm_eq
        have hk_even : k % 2 = 0 := m_even_of_sq k m' h2.symm
        obtain ⟨k', hk_eq⟩ := even_split k hk_even
        have h3 : m' * m' = 2 * (k' * k') := by
          rw [hk_eq] at h2
          have h_rearrange : (2 * k') * (2 * k') = 2 * (2 * (k' * k')) := by
            rw [mul_mul_mul_comm_local 2 k' 2 k']
            rw [mul_assoc_local 2 2 (k' * k')]
          rw [h_rearrange] at h2
          exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
        by_cases hk'_zero : k' = 0
        · apply hk
          rw [hk_eq, hk'_zero, Nat.mul_zero]
        · have hk'_pos : k' ≥ 1 := ne_zero_imp_ge_one k' hk'_zero
          have hbnd : 2 * k' ≤ n + 1 := by rw [← hk_eq]; exact hkn
          have hk'_le : k' ≤ n := half_lt_succ k' n hbnd hk'_pos
          exact hk'_zero (ih k' m' hk'_le h3)

/-- **√2 irrationality, ∅-axiom**: ∀ k ≥ 1, m, m * m ≠ 2 * (k * k). -/
theorem sqrt2_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 2 * (k * k) := by
  intro heq
  have h := sqrt2_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Lib.Math.Irrational.Sqrt2KernelFree
