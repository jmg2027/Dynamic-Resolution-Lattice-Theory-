import E213.Meta.Tactic.NatHelper

/-!
# Pow213 — power-of-2 + divisibility helpers (∅-axiom)

213-native replacements for Lean-core lemmas that bring `propext`
into power-of-2 / divisibility reasoning:

  - `Nat.pow_lt_pow_of_lt`   →  `pow_lt_pow_two`
  - `Nat.pow_dvd_pow`        →  `pow_dvd_pow_two`
  - `Nat.le_of_dvd`          →  `le_of_dvd_pos`
  - `Nat.dvd_sub`            →  `dvd_sub_two`

Plus the additive composition `pow_add_two : 2^(n+k) = 2^n * 2^k`.

Used by `Meta/BitPatternUniqueness.lean` and any file proving
2-adic valuation / power-of-2 claims.

Kernel-pure: no `rw` / `simp` / `decide`; only `Eq.subst` (`▸`),
`cases`, structural recursion, term-mode.
-/

namespace E213.Tactic.Pow213

open E213.Tactic.NatHelper (mul_assoc add_sub_of_le mul_sub_distrib)

/-- `0 < 2` without `decide`.  Used throughout this module. -/
private theorem zero_lt_two : 0 < 2 := Nat.zero_lt_succ 1

/-- `1 < 2` without `decide`. -/
private theorem one_lt_two : 1 < 2 := Nat.lt_succ_self 1

/-! ### powers of 2: monotone-strict + composition -/

/-- `2^a < 2^(a+1)`.  Single step.  Proof: `2^(a+1) = 2^a + 2^a`
    and `2^a > 0`, so RHS > LHS. -/
theorem pow_lt_succ (a : Nat) : 2^a < 2^(a+1) := by
  show 2^a < 2^a * 2
  exact (Nat.mul_two (2^a)).symm
        ▸ Nat.lt_add_of_pos_right (Nat.pos_pow_of_pos a zero_lt_two)

/-- `a < b → 2^a < 2^b`.  Replaces `Nat.pow_lt_pow_of_lt`
    (which brings propext). -/
theorem pow_lt_pow_two : ∀ (a b : Nat), a < b → 2^a < 2^b
  | _, 0,     h => absurd h (Nat.not_lt_zero _)
  | a, k + 1, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with ha_lt_k | ha_eq_k
      · exact Nat.lt_trans (pow_lt_pow_two a k ha_lt_k) (pow_lt_succ k)
      · exact ha_eq_k ▸ pow_lt_succ a

end E213.Tactic.Pow213

namespace E213.Tactic.Pow213

open E213.Tactic.NatHelper (mul_assoc add_sub_of_le mul_sub_distrib)

private theorem zero_lt_two' : 0 < 2 := Nat.zero_lt_succ 1

/-! ### additive composition: 2^(n+k) = 2^n * 2^k -/

/-- `2^(n+k) = 2^n * 2^k`.  Used in Frobenius-style cohomological
    decompositions and as the bridge between additive index
    arithmetic and multiplicative power growth. -/
theorem pow_add_two : ∀ (n k : Nat), 2^(n + k) = 2^n * 2^k
  | n, 0     => (Nat.mul_one _).symm
  | n, k + 1 => by
      show 2^(n + k) * 2 = 2^n * (2^k * 2)
      have ih : 2^(n + k) = 2^n * 2^k := pow_add_two n k
      have h1 : 2^(n+k) * 2 = 2^n * 2^k * 2 := ih ▸ rfl
      have h2 : 2^n * 2^k * 2 = 2^n * (2^k * 2) := mul_assoc _ _ _
      exact h1.trans h2

/-! ### divisibility-of-powers + dvd→le -/

/-- `n ≤ m → 2^n ∣ 2^m`.  Replaces `Nat.pow_dvd_pow` (propext).
    Witness: `2^(m-n)`. -/
theorem pow_dvd_pow_two (n m : Nat) (h : n ≤ m) : 2^n ∣ 2^m := by
  let k := m - n
  have heq : m = n + k := (add_sub_of_le h).symm
  have hadd : 2^(n + k) = 2^n * 2^k := pow_add_two n k
  refine ⟨2^k, ?_⟩
  exact heq ▸ hadd

/-- `0 < b → a ∣ b → a ≤ b`.  Replaces `Nat.le_of_dvd` (propext). -/
theorem le_of_dvd_pos (a b : Nat) (hb : 0 < b) (h : a ∣ b) : a ≤ b := by
  obtain ⟨c, hc⟩ := h
  cases c with
  | zero =>
      exfalso
      have hb0 : b = 0 := hc.trans (Nat.mul_zero a)
      exact Nat.lt_irrefl 0 (hb0 ▸ hb)
  | succ k =>
      have hge : a ≤ a * (k + 1) :=
        Nat.le_mul_of_pos_right a (Nat.zero_lt_succ _)
      exact hc ▸ hge

end E213.Tactic.Pow213

namespace E213.Tactic.Pow213

open E213.Tactic.NatHelper (mul_sub_distrib)

/-- `c ≤ b → a ∣ b → a ∣ c → a ∣ b - c`.
    Replaces `Nat.dvd_sub` (propext). -/
theorem dvd_sub_two (a b c : Nat) (h : c ≤ b) (hb : a ∣ b) (hc : a ∣ c) :
    a ∣ b - c := by
  obtain ⟨x, hx⟩ := hb
  obtain ⟨y, hy⟩ := hc
  rcases Nat.eq_zero_or_pos a with ha0 | hap
  · -- a = 0: both b and c are 0, so b - c = 0 = 0 * 0.
    subst ha0
    have hb0 : b = 0 := hx.trans (Nat.zero_mul x)
    have hc0 : c = 0 := hy.trans (Nat.zero_mul y)
    refine ⟨0, ?_⟩
    have hbc0 : b - c = 0 := hb0 ▸ hc0 ▸ rfl
    exact hbc0.trans (Nat.zero_mul 0).symm
  · -- a > 0: derive y ≤ x from c ≤ b by mul-monotonicity.
    have hyx : y ≤ x := by
      rcases Nat.lt_or_ge x y with hxy | hyx
      · exfalso
        have hlt : a * x < a * y := Nat.mul_lt_mul_of_pos_left hxy hap
        have hle : a * y ≤ a * x := hy ▸ hx ▸ h
        exact absurd hlt (Nat.not_lt.mpr hle)
      · exact hyx
    refine ⟨x - y, ?_⟩
    have step1 : b - c = a * x - a * y := hx ▸ hy ▸ rfl
    have step2 : a * x - a * y = a * (x - y) :=
      (@mul_sub_distrib x y a hyx).symm
    exact step1.trans step2

end E213.Tactic.Pow213
