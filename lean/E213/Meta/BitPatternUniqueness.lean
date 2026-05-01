/-!
# Bit-pattern uniqueness — key lemma for expSumLens injectivity

The fundamental lemma:
  `2^m + 2^n = 2^p + 2^q ∧ m < n ∧ p < q → m = p ∧ n = q`

Proof technique: factor out lowest-power-of-2.  If m ≠ p, divide
both sides by 2^min(m,p) and observe an odd-vs-even contradiction.

213-native (≤ {propext, Quot.sound}, no Mathlib).
-/

namespace E213.Meta.BitPatternUniqueness

/-- ★★★★★★ Key uniqueness lemma: if 2^m + 2^n = 2^p + 2^q with
    m < n and p < q, then m = p and n = q. -/
theorem two_pow_sum_inj_lt
    (m n p q : Nat) (hmn : m < n) (hpq : p < q)
    (heq : 2^m + 2^n = 2^p + 2^q) : m = p ∧ n = q := by
  rcases Nat.lt_trichotomy m p with hlt | heqmp | hgt
  · have hpos : 0 < 2^m := Nat.pos_pow_of_pos _ (by decide)
    have h_factor_l : 2^m + 2^n = 2^m * (1 + 2^(n-m)) := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add]
      congr 2; omega
    have h_factor_r : 2^p + 2^q = 2^m * (2^(p-m) + 2^(q-m)) := by
      rw [Nat.mul_add, ← Nat.pow_add, ← Nat.pow_add]
      congr 2 <;> omega
    rw [h_factor_l, h_factor_r] at heq
    have heq' : 1 + 2^(n-m) = 2^(p-m) + 2^(q-m) :=
      Nat.eq_of_mul_eq_mul_left hpos heq
    have h_lhs_odd : (1 + 2^(n-m)) % 2 = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      rw [hk, Nat.pow_succ]
      have e : 2^k * 2 % 2 = 0 := Nat.mul_mod_left _ _
      omega
    have h_rhs_even : (2^(p-m) + 2^(q-m)) % 2 = 0 := by
      obtain ⟨k1, hk1⟩ : ∃ k, p - m = k + 1 := ⟨p - m - 1, by omega⟩
      obtain ⟨k2, hk2⟩ : ∃ k, q - m = k + 1 := ⟨q - m - 1, by omega⟩
      rw [hk1, hk2, Nat.pow_succ, Nat.pow_succ]
      have e1 : 2^k1 * 2 % 2 = 0 := Nat.mul_mod_left _ _
      have e2 : 2^k2 * 2 % 2 = 0 := Nat.mul_mod_left _ _
      omega
    rw [heq'] at h_lhs_odd; omega
  · refine ⟨heqmp, ?_⟩
    rw [heqmp] at heq
    have h_pow_eq : 2^n = 2^q := by omega
    rcases Nat.lt_trichotomy n q with hlt | heq2 | hgt
    · have : 2^n < 2^q := Nat.pow_lt_pow_of_lt (by decide) hlt
      omega
    · exact heq2
    · have : 2^q < 2^n := Nat.pow_lt_pow_of_lt (by decide) hgt
      omega
  · have hpos : 0 < 2^p := Nat.pos_pow_of_pos _ (by decide)
    have h_factor_l : 2^m + 2^n = 2^p * (2^(m-p) + 2^(n-p)) := by
      rw [Nat.mul_add, ← Nat.pow_add, ← Nat.pow_add]
      congr 2 <;> omega
    have h_factor_r : 2^p + 2^q = 2^p * (1 + 2^(q-p)) := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add]
      congr 2; omega
    rw [h_factor_l, h_factor_r] at heq
    have heq' : 2^(m-p) + 2^(n-p) = 1 + 2^(q-p) :=
      Nat.eq_of_mul_eq_mul_left hpos heq
    have h_lhs_even : (2^(m-p) + 2^(n-p)) % 2 = 0 := by
      obtain ⟨k1, hk1⟩ : ∃ k, m - p = k + 1 := ⟨m - p - 1, by omega⟩
      obtain ⟨k2, hk2⟩ : ∃ k, n - p = k + 1 := ⟨n - p - 1, by omega⟩
      rw [hk1, hk2, Nat.pow_succ, Nat.pow_succ]
      have e1 : 2^k1 * 2 % 2 = 0 := Nat.mul_mod_left _ _
      have e2 : 2^k2 * 2 % 2 = 0 := Nat.mul_mod_left _ _
      omega
    have h_rhs_odd : (1 + 2^(q-p)) % 2 = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, q - p = k + 1 := ⟨q - p - 1, by omega⟩
      rw [hk, Nat.pow_succ]
      have : 2^k * 2 % 2 = 0 := Nat.mul_mod_left _ _
      omega
    rw [heq'] at h_lhs_even; omega

/-- ★★★★★★ Unordered version: 2^m + 2^n = 2^p + 2^q with m ≠ n
    and p ≠ q implies {m, n} = {p, q} as unordered pairs. -/
theorem two_pow_sum_inj_unordered
    (m n p q : Nat) (hmn : m ≠ n) (hpq : p ≠ q)
    (heq : 2^m + 2^n = 2^p + 2^q) :
    (m = p ∧ n = q) ∨ (m = q ∧ n = p) := by
  rcases Nat.lt_or_gt_of_ne hmn with hmn' | hmn'
  · rcases Nat.lt_or_gt_of_ne hpq with hpq' | hpq'
    · left; exact two_pow_sum_inj_lt m n p q hmn' hpq' heq
    · right
      have heq' : 2^m + 2^n = 2^q + 2^p := by
        rw [heq, Nat.add_comm]
      exact two_pow_sum_inj_lt m n q p hmn' hpq' heq'
  · rcases Nat.lt_or_gt_of_ne hpq with hpq' | hpq'
    · right
      have heq' : 2^n + 2^m = 2^p + 2^q := by
        rw [Nat.add_comm]; exact heq
      have ⟨h1, h2⟩ := two_pow_sum_inj_lt n m p q hmn' hpq' heq'
      exact ⟨h2, h1⟩
    · left
      have heq' : 2^n + 2^m = 2^q + 2^p := by
        rw [Nat.add_comm (2^n) (2^m), heq, Nat.add_comm]
      have ⟨h1, h2⟩ := two_pow_sum_inj_lt n m q p hmn' hpq' heq'
      exact ⟨h2, h1⟩

/-- Helper: 2^m + 2^n with m < n is NOT a single power of 2.
    Proof via 2-adic valuation: 2^m | LHS but 2^(m+1) ∤ LHS,
    while 2^(m+1) | 2^k for k > m. -/
theorem two_pow_sum_lt_not_pow (m n : Nat) (hmn : m < n) :
    ∀ k, 2^m + 2^n ≠ 2^k := by
  intro k heq
  have h_lhs_gt : 2^m + 2^n > 2^m := by
    have : 0 < 2^n := Nat.pos_pow_of_pos _ (by decide)
    omega
  have hk_gt_m : k > m := by
    rw [heq] at h_lhs_gt
    rcases Nat.lt_or_ge m k with h | h
    · exact h
    · exfalso
      have : 2^k ≤ 2^m := Nat.pow_le_pow_right (by decide) h
      omega
  have h_dvd_rhs : 2^(m+1) ∣ 2^k := Nat.pow_dvd_pow 2 hk_gt_m
  rw [← heq] at h_dvd_rhs
  have h_dvd_2n : 2^(m+1) ∣ 2^n := Nat.pow_dvd_pow 2 hmn
  have h_dvd_2m : 2^(m+1) ∣ 2^m := by
    have h2n_le : 2^n ≤ 2^m + 2^n := Nat.le_add_left _ _
    have hd : 2^(m+1) ∣ (2^m + 2^n) - 2^n :=
      Nat.dvd_sub h2n_le h_dvd_rhs h_dvd_2n
    have hsub : 2^m + 2^n - 2^n = 2^m := by omega
    rw [hsub] at hd; exact hd
  have h1 : 2^(m+1) ≤ 2^m :=
    Nat.le_of_dvd (Nat.pos_pow_of_pos _ (by decide)) h_dvd_2m
  have h2 : 2^m < 2^(m+1) := by
    rw [Nat.pow_succ]
    have : 0 < 2^m := Nat.pos_pow_of_pos _ (by decide)
    omega
  omega

/-- ★★★ Distinct LHS exponents force distinct RHS exponents:
    if 2^m + 2^n = 2^p + 2^q and m ≠ n, then p ≠ q. -/
theorem two_pow_sum_distinct_forces_distinct
    (m n p q : Nat) (hmn : m ≠ n)
    (heq : 2^m + 2^n = 2^p + 2^q) : p ≠ q := by
  intro hpq
  rw [hpq] at heq
  have hsum : 2^q + 2^q = 2^(q+1) := by
    rw [Nat.pow_succ]; omega
  rw [hsum] at heq
  rcases Nat.lt_or_gt_of_ne hmn with hmn' | hmn'
  · exact two_pow_sum_lt_not_pow m n hmn' (q+1) heq
  · have : 2^n + 2^m = 2^(q+1) := by rw [Nat.add_comm]; exact heq
    exact two_pow_sum_lt_not_pow n m hmn' (q+1) this

/-- ★★★★★★★ FULL unordered uniqueness: 2^m + 2^n = 2^p + 2^q with
    m ≠ n implies {m, n} = {p, q} as unordered pairs.
    The right-side distinctness p ≠ q is DERIVED automatically. -/
theorem two_pow_sum_inj_full
    (m n p q : Nat) (hmn : m ≠ n)
    (heq : 2^m + 2^n = 2^p + 2^q) :
    (m = p ∧ n = q) ∨ (m = q ∧ n = p) :=
  two_pow_sum_inj_unordered m n p q hmn
    (two_pow_sum_distinct_forces_distinct m n p q hmn heq) heq

end E213.Meta.BitPatternUniqueness
