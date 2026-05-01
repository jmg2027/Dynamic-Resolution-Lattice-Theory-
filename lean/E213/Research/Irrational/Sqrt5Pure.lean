import E213.Research.ModArith.PureNatMod5

/-!
# Research.Sqrt5IrrationalPure: √5 irrationality, **truly axiom-free**

Generalization of `Sqrt2IrrationalPure` + `Sqrt3IrrationalPure` to p = 5.
Same 5-step descent template — evidence of robustness of descent for *prime* p.

## Observations

- p = 2: 2 cases (even/odd).
- p = 3: 3 cases (mod 0/1/2).
- p = 5: 5 cases (mod 0/1/2/3/4).
- p = 7: 7 cases (expected).

The case-count grows for each prime p, but the 5-step template is
*mechanical*.  The essence of irrationality = squaring kernel of (Z/p)*
trivial.
-/

namespace E213.Research.Sqrt5IrrationalPure

open E213.Research.PureNat
open E213.Research.PureNatMod5

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

end E213.Research.Sqrt5IrrationalPure
