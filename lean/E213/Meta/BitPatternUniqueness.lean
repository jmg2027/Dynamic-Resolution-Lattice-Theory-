import E213.Meta.Tactic.Pow213
import E213.Meta.Tactic.Mod213
import E213.Meta.Tactic.NatHelper

/-!
# Bit-pattern uniqueness — key lemma for expSumLens injectivity (∅-axiom)

The fundamental lemma:
  `2^m + 2^n = 2^p + 2^q ∧ m < n ∧ p < q → m = p ∧ n = q`

Proof technique (213-native): factor out `2^min(m,p)`.  After
cancelling `2^m`, the LHS has the shape `1 + 2^(d+1)` (parity =
true, since `parity 1 = true` and `parity (2^(k+1)) = false`), and
the RHS has the shape `2^(a+1) + 2^(b+1)` (parity = false).
Contradiction by parity.

To stay strict ∅-axiom (avoiding the `propext` / `Quot.sound` that
`% 2` + `omega` would import), this uses 213-native `Mod213.parity`
(step-2 cohomological residue) + `Pow213.{pow_dvd_pow_two,
le_of_dvd_pos, dvd_sub_two, pow_lt_pow_two}` + `Nat213.{add_left_cancel,
le_sub_of_add_le, sub_one_add_one, add_sub_of_le, add_sub_cancel_right}`.

All 5 public theorems strict ∅-axiom.
-/

namespace E213.Meta.BitPatternUniqueness

open E213.Tactic.Pow213 E213.Tactic.Mod213
open E213.Tactic.NatHelper
  (sub_one_add_one le_sub_of_add_le add_sub_of_le
   add_sub_cancel_right add_left_cancel)

/-! ### Helpers -/

private theorem ge_one_sub (m n : Nat) (h : m < n) : 1 ≤ n - m := by
  have h1 : m + 1 ≤ n := Nat.succ_le_of_lt h
  have h1' : 1 + m ≤ n := Nat.add_comm m 1 ▸ h1
  exact le_sub_of_add_le h1'

private theorem sub_succ_form (m n : Nat) (h : m < n) :
    n - m = (n - m - 1) + 1 := by
  have h2 := ge_one_sub m n h
  have hne : n - m ≠ 0 := fun heq =>
    Nat.not_succ_le_zero 0 (heq ▸ h2 : (1 : Nat) ≤ 0)
  exact (sub_one_add_one hne).symm

private theorem factor_lhs (m n : Nat) (h : m < n) :
    2^m + 2^n = 2^m * (1 + 2^(n - m)) := by
  let d := n - m
  have hadd : n = m + d := (add_sub_of_le (Nat.le_of_lt h)).symm
  have hpow : 2^n = 2^m * 2^d := hadd ▸ pow_add_two m d
  have step1 : 2^m + 2^n = 2^m + 2^m * 2^d := hpow ▸ rfl
  have step2 : 2^m + 2^m * 2^d = 2^m * 1 + 2^m * 2^d := by rw [Nat.mul_one]
  have step3 : 2^m * 1 + 2^m * 2^d = 2^m * (1 + 2^d) :=
    (Nat.mul_add (2^m) 1 (2^d)).symm
  exact step1.trans (step2.trans step3)

private theorem factor_rhs (m p q : Nat) (hmp : m ≤ p) (hmq : m ≤ q) :
    2^p + 2^q = 2^m * (2^(p - m) + 2^(q - m)) := by
  let dp := p - m
  let dq := q - m
  have hadd_p : p = m + dp := (add_sub_of_le hmp).symm
  have hadd_q : q = m + dq := (add_sub_of_le hmq).symm
  have hpow_p : 2^p = 2^m * 2^dp := hadd_p ▸ pow_add_two m dp
  have hpow_q : 2^q = 2^m * 2^dq := hadd_q ▸ pow_add_two m dq
  have step1 : 2^p + 2^q = 2^m * 2^dp + 2^m * 2^dq := hpow_p ▸ hpow_q ▸ rfl
  have step2 : 2^m * 2^dp + 2^m * 2^dq = 2^m * (2^dp + 2^dq) :=
    (Nat.mul_add _ _ _).symm
  exact step1.trans step2

/-- Parity contradiction: `1 + 2^(d+1) ≠ 2^(a+1) + 2^(b+1)`.
    LHS has parity `true`, RHS has parity `false`. -/
private theorem parity_contradiction (d a b : Nat)
    (heq : 1 + 2^(d + 1) = 2^(a + 1) + 2^(b + 1)) : False := by
  have hL : parity (1 + 2^(d + 1)) = true := by
    have h := parity_add 1 (2^(d + 1))
    have hp : parity (2^(d + 1)) = false := parity_pow_two_succ d
    rw [h, hp]; rfl
  have hR : parity (2^(a + 1) + 2^(b + 1)) = false := by
    have h := parity_add (2^(a + 1)) (2^(b + 1))
    have hp1 : parity (2^(a + 1)) = false := parity_pow_two_succ a
    have hp2 : parity (2^(b + 1)) = false := parity_pow_two_succ b
    rw [h, hp1, hp2]; rfl
  have htrue : parity (2^(a + 1) + 2^(b + 1)) = true := heq ▸ hL
  exact Bool.noConfusion (htrue.symm.trans hR)


/-- ★★★★★★ Key uniqueness lemma: if `2^m + 2^n = 2^p + 2^q` with
    `m < n` and `p < q`, then `m = p` and `n = q`. -/
theorem two_pow_sum_inj_lt
    (m n p q : Nat) (hmn : m < n) (hpq : p < q)
    (heq : 2^m + 2^n = 2^p + 2^q) : m = p ∧ n = q := by
  rcases Nat.lt_trichotomy m p with hlt | heqmp | hgt
  · -- case m < p
    have hmq : m < q := Nat.lt_trans hlt hpq
    have hL : 2^m + 2^n = 2^m * (1 + 2^(n - m)) := factor_lhs m n hmn
    have hR : 2^p + 2^q = 2^m * (2^(p - m) + 2^(q - m)) :=
      factor_rhs m p q (Nat.le_of_lt hlt) (Nat.le_of_lt hmq)
    have hcanc : 2^m * (1 + 2^(n - m)) = 2^m * (2^(p - m) + 2^(q - m)) :=
      hL.symm.trans (heq.trans hR)
    have hpos : 0 < 2^m := Nat.pos_pow_of_pos _ (Nat.zero_lt_succ 1)
    have heq' : 1 + 2^(n - m) = 2^(p - m) + 2^(q - m) :=
      Nat.eq_of_mul_eq_mul_left hpos hcanc
    have hd : n - m = (n - m - 1) + 1 := sub_succ_form m n hmn
    have ha : p - m = (p - m - 1) + 1 := sub_succ_form m p hlt
    have hb : q - m = (q - m - 1) + 1 := sub_succ_form m q hmq
    have heq'' : 1 + 2^((n - m - 1) + 1)
                = 2^((p - m - 1) + 1) + 2^((q - m - 1) + 1) :=
      hd ▸ ha ▸ hb ▸ heq'
    exact absurd heq'' (fun h => parity_contradiction _ _ _ h)
  · -- case m = p
    refine ⟨heqmp, ?_⟩
    have heq2 : 2^m + 2^n = 2^m + 2^q := heqmp ▸ heq
    have hpow_eq : 2^n = 2^q := add_left_cancel heq2
    rcases Nat.lt_trichotomy n q with hnq | hnq | hnq
    · exact absurd (hpow_eq.symm ▸ pow_lt_pow_two n q hnq : 2^n < 2^n)
        (Nat.lt_irrefl _)
    · exact hnq
    · exact absurd (hpow_eq ▸ pow_lt_pow_two q n hnq : 2^q < 2^q)
        (Nat.lt_irrefl _)
  · -- case m > p (symmetric to m < p, swap roles)
    have hpn : p < n := Nat.lt_trans hgt hmn
    have hL : 2^p + 2^q = 2^p * (1 + 2^(q - p)) := factor_lhs p q hpq
    have hR : 2^m + 2^n = 2^p * (2^(m - p) + 2^(n - p)) :=
      factor_rhs p m n (Nat.le_of_lt hgt) (Nat.le_of_lt hpn)
    have hcanc : 2^p * (1 + 2^(q - p)) = 2^p * (2^(m - p) + 2^(n - p)) :=
      hL.symm.trans (heq.symm.trans hR)
    have hpos : 0 < 2^p := Nat.pos_pow_of_pos _ (Nat.zero_lt_succ 1)
    have heq' : 1 + 2^(q - p) = 2^(m - p) + 2^(n - p) :=
      Nat.eq_of_mul_eq_mul_left hpos hcanc
    have hd : q - p = (q - p - 1) + 1 := sub_succ_form p q hpq
    have ha : m - p = (m - p - 1) + 1 := sub_succ_form p m hgt
    have hb : n - p = (n - p - 1) + 1 := sub_succ_form p n hpn
    have heq'' : 1 + 2^((q - p - 1) + 1)
                = 2^((m - p - 1) + 1) + 2^((n - p - 1) + 1) :=
      hd ▸ ha ▸ hb ▸ heq'
    exact absurd heq'' (fun h => parity_contradiction _ _ _ h)


/-- ★★★★★★ Unordered version: `2^m + 2^n = 2^p + 2^q` with `m ≠ n`
    and `p ≠ q` implies `{m, n} = {p, q}` as unordered pairs. -/
theorem two_pow_sum_inj_unordered
    (m n p q : Nat) (hmn : m ≠ n) (hpq : p ≠ q)
    (heq : 2^m + 2^n = 2^p + 2^q) :
    (m = p ∧ n = q) ∨ (m = q ∧ n = p) := by
  rcases Nat.lt_or_gt_of_ne hmn with hmn' | hmn'
  · rcases Nat.lt_or_gt_of_ne hpq with hpq' | hpq'
    · exact Or.inl (two_pow_sum_inj_lt m n p q hmn' hpq' heq)
    · have heq' : 2^m + 2^n = 2^q + 2^p := heq.trans (Nat.add_comm _ _)
      exact Or.inr (two_pow_sum_inj_lt m n q p hmn' hpq' heq')
  · rcases Nat.lt_or_gt_of_ne hpq with hpq' | hpq'
    · have heq' : 2^n + 2^m = 2^p + 2^q := (Nat.add_comm _ _).trans heq
      have ⟨h1, h2⟩ := two_pow_sum_inj_lt n m p q hmn' hpq' heq'
      exact Or.inr ⟨h2, h1⟩
    · have heq' : 2^n + 2^m = 2^q + 2^p :=
        (Nat.add_comm _ _).trans (heq.trans (Nat.add_comm _ _))
      have ⟨h1, h2⟩ := two_pow_sum_inj_lt n m q p hmn' hpq' heq'
      exact Or.inl ⟨h2, h1⟩

/-- Helper: `2^m + 2^n` with `m < n` is NOT a single power of 2.
    Proof via 2-adic valuation: `2^m | LHS` but `2^(m+1) ∤ LHS`,
    while `2^(m+1) | 2^k` for `k > m`. -/
theorem two_pow_sum_lt_not_pow (m n : Nat) (hmn : m < n) :
    ∀ k, 2^m + 2^n ≠ 2^k := by
  intro k heq
  have h_pos_n : 0 < 2^n := Nat.pos_pow_of_pos _ (Nat.zero_lt_succ 1)
  have h_lhs_gt : 2^m < 2^m + 2^n := Nat.lt_add_of_pos_right h_pos_n
  have hk_gt_m : k > m := by
    rcases Nat.lt_or_ge m k with h | h
    · exact h
    · exfalso
      have h1 : 2^k ≤ 2^m := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) h
      have h2 : 2^m < 2^k := heq ▸ h_lhs_gt
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h1)
  have h_dvd_rhs : 2^(m+1) ∣ 2^k := pow_dvd_pow_two (m+1) k hk_gt_m
  have h_dvd_lhs : 2^(m+1) ∣ 2^m + 2^n := heq.symm ▸ h_dvd_rhs
  have h_dvd_2n : 2^(m+1) ∣ 2^n := pow_dvd_pow_two (m+1) n hmn
  have h2n_le : 2^n ≤ 2^m + 2^n := Nat.le_add_left _ _
  have h_dvd_2m : 2^(m+1) ∣ 2^m := by
    have hd : 2^(m+1) ∣ (2^m + 2^n) - 2^n :=
      dvd_sub_two _ _ _ h2n_le h_dvd_lhs h_dvd_2n
    have hsub : 2^m + 2^n - 2^n = 2^m := add_sub_cancel_right (2^m) (2^n)
    exact hsub ▸ hd
  have h_pos_m : 0 < 2^m := Nat.pos_pow_of_pos _ (Nat.zero_lt_succ 1)
  have h1 : 2^(m+1) ≤ 2^m := le_of_dvd_pos _ _ h_pos_m h_dvd_2m
  have h2 : 2^m < 2^(m+1) := pow_lt_succ m
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h1)

/-- ★★★ Distinct LHS exponents force distinct RHS exponents:
    if `2^m + 2^n = 2^p + 2^q` and `m ≠ n`, then `p ≠ q`. -/
theorem two_pow_sum_distinct_forces_distinct
    (m n p q : Nat) (hmn : m ≠ n)
    (heq : 2^m + 2^n = 2^p + 2^q) : p ≠ q := by
  intro hpq
  have heq' : 2^m + 2^n = 2^q + 2^q := hpq ▸ heq
  have hsum : 2^q + 2^q = 2^(q+1) := (Nat.mul_two _).symm
  have heq'' : 2^m + 2^n = 2^(q+1) := heq'.trans hsum
  rcases Nat.lt_or_gt_of_ne hmn with hmn' | hmn'
  · exact two_pow_sum_lt_not_pow m n hmn' (q+1) heq''
  · have hcomm : 2^n + 2^m = 2^(q+1) := (Nat.add_comm _ _).trans heq''
    exact two_pow_sum_lt_not_pow n m hmn' (q+1) hcomm

/-- ★★★★★★★ FULL unordered uniqueness: `2^m + 2^n = 2^p + 2^q` with
    `m ≠ n` implies `{m, n} = {p, q}` as unordered pairs.
    The right-side distinctness `p ≠ q` is DERIVED automatically. -/
theorem two_pow_sum_inj_full
    (m n p q : Nat) (hmn : m ≠ n)
    (heq : 2^m + 2^n = 2^p + 2^q) :
    (m = p ∧ n = q) ∨ (m = q ∧ n = p) :=
  two_pow_sum_inj_unordered m n p q hmn
    (two_pow_sum_distinct_forces_distinct m n p q hmn heq) heq

end E213.Meta.BitPatternUniqueness
