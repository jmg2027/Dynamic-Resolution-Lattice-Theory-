import E213.Firmware.Raw

/-!
# Research.Sqrt2Irrational: m² = 2k² impossible (k ≥ 1)

Elevates the input fact "irrationality of √2" from `Sqrt2Cut` to a
framework-internal lemma.  Uses only Lean 4 core + descent.

## Core

`sqrt2_irrational`: ∀ k ≥ 1, ∀ m : ℕ, m * m ≠ 2 * k * k.

Proof: 2-adic descent.  m² = 2k² → m even → m = 2m' →
4m'² = 2k² → k² = 2m'² → k even → k = 2k' → m'² = 2k'² →
k' < k so apply induction hypothesis.
-/

namespace E213.Math.Irrational.Sqrt2

/-- The parity of `m * m` matches the parity of `m`. -/
theorem mul_self_mod_two (m : Nat) : m * m % 2 = m % 2 := by
  have h := Nat.mod_two_eq_zero_or_one m
  rcases h with h | h
  · -- m even: m = 2k, m*m = 4 k² → mod 2 = 0
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    have h1 : 2 * k * (2 * k) = 4 * (k * k) := by
      rw [Nat.mul_mul_mul_comm]
    have hK := k * k  -- atomize k*k
    rw [h1]; omega
  · -- m odd: m = 2k+1, m*m = 4k² + 4k + 1 → mod 2 = 1
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    have h1 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k) + 4 * k + 1 := by
      have e0 : (2*k+1) * (2*k+1) = 2*k*(2*k+1) + 1*(2*k+1) := Nat.add_mul _ _ _
      have e1 : 2*k*(2*k+1) = 2*k*(2*k) + 2*k*1 := Nat.mul_add _ _ _
      have e2 : 1*(2*k+1) = 1*(2*k) + 1*1 := Nat.mul_add _ _ _
      have e3 : 2*k*(2*k) = 4 * (k*k) := Nat.mul_mul_mul_comm _ _ _ _
      rw [e0, e1, e2, e3]; omega
    rw [h1]; omega

end E213.Math.Irrational.Sqrt2

namespace E213.Math.Irrational.Sqrt2

/-- Descent step for `m * m = 2 * k * k`:
    m even → m = 2m', 2 * (m'*m') = k*k. -/
private theorem descent_step (m k : Nat) (heq : m * m = 2 * (k * k))
    (m' : Nat) (hm : m = 2 * m') :
    2 * (m' * m') = k * k := by
  have h1 : (2 * m') * (2 * m') = 4 * (m' * m') := Nat.mul_mul_mul_comm _ _ _ _
  rw [hm, h1] at heq
  -- 4 * (m' * m') = 2 * (k * k) → 2 * (m' * m') = k * k
  omega

end E213.Math.Irrational.Sqrt2

namespace E213.Math.Irrational.Sqrt2

/-- **Auxiliary descent**: bounded by `s` (s ≥ k), descent
    works step-by-step.  If k is even then m is even; halving both
    gives a smaller instance — induction on `s`. -/
theorem sqrt2_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 2 * (k * k) → k = 0 := by
  intro s
  induction s with
  | zero =>
      intro k _ hkn _
      omega
  | succ n ih =>
      intro k m hkn heq
      by_cases hk : k = 0
      · exact hk
      · exfalso
        -- m * m even → m even
        have hm_even : m % 2 = 0 := by
          rw [← mul_self_mod_two]; omega
        obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
        have h2 : 2 * (m' * m') = k * k := descent_step _ _ heq m' rfl
        have hk_even : k % 2 = 0 := by
          rw [← mul_self_mod_two]; omega
        obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
        have h3 : (2 * k') * (2 * k') = 4 * (k' * k') :=
          Nat.mul_mul_mul_comm _ _ _ _
        rw [h3] at h2
        have h4 : m' * m' = 2 * (k' * k') := by omega
        have hk'_le : k' ≤ n := by omega
        have hk'_zero : k' = 0 := ih k' m' hk'_le h4
        omega

end E213.Math.Irrational.Sqrt2

namespace E213.Math.Irrational.Sqrt2

/-- **Irrationality of √2, framework-internal**: ∀ k, m: ℕ,
    m² = 2 k² → k = 0.

    Combined with `PellSeq`'s invariant `IsPellSol x y := x² = 2y² + 1`,
    no (m, k) with k ≥ 1 can satisfy m² = 2k².  That is,
    no k ≥ 1 allows a rational √2 = m/k.

    The input fact of `Sqrt2Cut` is elevated to a framework-internal lemma
    — Pell-style descent (Lean 4 core + omega). -/
theorem sqrt2_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 2 * (k * k) := by
  intro heq
  have h := sqrt2_no_rational_aux k k m (Nat.le_refl _) heq
  omega

end E213.Math.Irrational.Sqrt2
