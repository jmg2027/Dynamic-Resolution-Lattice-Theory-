import E213.Meta.Nat.Valuation
import E213.Meta.Nat.SubMod213

/-!
# Grounded `q`-adic valuation `vpSub` — `subMod`-based, `Nat.mod`-free (∅-axiom)

`Meta/Nat/Valuation.vp` decides each step on `n % qᵏ = 0` — clean `decEq` on the *result* of `Nat.mod`,
but `Nat.mod` itself carries `Nat.lt_wfRel`/`WellFounded.fix` (verified: `vp` closure has `Nat.mod`,
`Nat.lt_wfRel`).  This file rebuilds the identical downward search on `subMod` (the structural,
`lt_wfRel`-free remainder of `SubMod213`), bridging the divisibility decision through
`subMod_zero_iff_dvd` instead of `dvd_of_mod_eq_zero`/`mod_zero_of_dvd`.  The clean
`drefl`/`dtrans`/`pow_dvd_of_le`/`le_of_dvd_pos`/`lt_two_pow` helpers are reused verbatim.

  * `vpSub q n` — largest `k` with `qᵏ ∣ n`, via `subMod`.
  * `pow_vpSub_dvd` — `q^(vpSub q n) ∣ n`.
  * `vpSub_not_dvd_succ` — `q^(vpSub q n + 1) ∤ n` (exactness, `q ≥ 2`, `n > 0`).
  * `le_vpSub_iff` — `qᵏ ∣ n ⟺ k ≤ vpSub q n`.

∅-axiom; no `Nat.mod`/`Nat.div`/`Nat.lt_wfRel`.
-/

namespace E213.Meta.Nat.VpSub213

open E213.Meta.Nat.Valuation (drefl dtrans pow_dvd_of_le)
open E213.Meta.Nat.SubMod213 (subMod subMod_zero_iff_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.PureNat (lt_two_pow)

/-! ## §1 — the search, on `subMod` -/

/-- Downward search for the largest `k ≤ b` with `qᵏ ∣ n`, deciding on `subMod n n (qᵏ) = 0` (the
    `Nat.mod`-free divisibility test).  Structural `Nat.rec` on `b`. -/
def vpSubSearch (q n : Nat) : Nat → Nat
  | 0     => 0
  | k + 1 => if subMod n n (q ^ (k + 1)) = 0 then k + 1 else vpSubSearch q n k

/-- The grounded `q`-adic valuation of `n`. -/
def vpSub (q n : Nat) : Nat := vpSubSearch q n n

/-- `q^(vpSubSearch q n b) ∣ n` (`0 < q`, for the positive power feeding `subMod_zero_iff_dvd`). -/
theorem vpSubSearch_dvd (q n : Nat) (hq : 0 < q) : ∀ b, q ^ (vpSubSearch q n b) ∣ n
  | 0     => ⟨n, (Nat.one_mul n).symm⟩
  | b + 1 => by
    show q ^ (vpSubSearch q n (b + 1)) ∣ n
    unfold vpSubSearch
    by_cases h : subMod n n (q ^ (b + 1)) = 0
    · rw [if_pos h]
      exact (subMod_zero_iff_dvd n (q ^ (b + 1)) (Nat.pos_pow_of_pos (b + 1) hq)).mp h
    · rw [if_neg h]; exact vpSubSearch_dvd q n hq b

theorem vpSubSearch_le (q n : Nat) : ∀ b, vpSubSearch q n b ≤ b
  | 0     => Nat.le_refl 0
  | b + 1 => by
    unfold vpSubSearch
    by_cases h : subMod n n (q ^ (b + 1)) = 0
    · rw [if_pos h]; exact Nat.le_refl _
    · rw [if_neg h]; exact Nat.le_succ_of_le (vpSubSearch_le q n b)

theorem vpSubSearch_ge (q n : Nat) (hq : 2 ≤ q) :
    ∀ b k, k ≤ b → q ^ k ∣ n → k ≤ vpSubSearch q n b
  | 0,     k, hk, _ => Nat.le_trans hk (Nat.le_refl 0)
  | b + 1, k, hk, h => by
    unfold vpSubSearch
    by_cases hc : subMod n n (q ^ (b + 1)) = 0
    · rw [if_pos hc]; exact hk
    · rw [if_neg hc]
      have hkb : k ≤ b := by
        rcases Nat.lt_or_eq_of_le hk with hlt | heq
        · exact Nat.le_of_lt_succ hlt
        · subst heq
          exact absurd ((subMod_zero_iff_dvd n (q ^ (b + 1))
            (Nat.pos_pow_of_pos (b + 1) (Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hq))).mpr h) hc
      exact vpSubSearch_ge q n hq b k hkb h

/-! ## §2 — `vpSub` laws (mirror `Valuation` §2) -/

theorem pow_vpSub_dvd (q n : Nat) (hq : 0 < q) : q ^ (vpSub q n) ∣ n := vpSubSearch_dvd q n hq n

theorem vpSub_ge (q n k : Nat) (hq : 2 ≤ q) (hk : k ≤ n) (h : q ^ k ∣ n) : k ≤ vpSub q n :=
  vpSubSearch_ge q n hq n k hk h

theorem vpSub_lt (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) : vpSub q n < n := by
  have hq0 : 0 < q := Nat.lt_of_lt_of_le (by decide) hq
  rcases Nat.lt_or_ge (vpSub q n) n with hlt | hge
  · exact hlt
  · exfalso
    have hvpe : vpSub q n = n := Nat.le_antisymm (vpSubSearch_le q n n) hge
    have hdvd : q ^ n ∣ n := by have hd := pow_vpSub_dvd q n hq0; rwa [hvpe] at hd
    have hqn : n < q ^ n :=
      Nat.lt_of_lt_of_le (lt_two_pow n) (Nat.pow_le_pow_left hq n)
    exact absurd (le_of_dvd_pos (q ^ n) n hn hdvd) (Nat.not_le.mpr hqn)

theorem vpSub_not_dvd_succ (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) : ¬ q ^ (vpSub q n + 1) ∣ n := by
  intro h
  have hle : vpSub q n + 1 ≤ n := vpSub_lt q n hq hn
  exact absurd (vpSub_ge q n (vpSub q n + 1) hq hle h) (Nat.not_succ_le_self (vpSub q n))

theorem le_vpSub_iff (q n k : Nat) (hq : 2 ≤ q) (hn : 0 < n) : q ^ k ∣ n ↔ k ≤ vpSub q n := by
  have hq0 : 0 < q := Nat.lt_of_lt_of_le (by decide) hq
  constructor
  · intro h
    rcases Nat.lt_or_ge k n with hkn | hkn
    · exact vpSub_ge q n k hq (Nat.le_of_lt hkn) h
    · exfalso
      have hqk : n < q ^ k :=
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (lt_two_pow n) (Nat.pow_le_pow_left hq n))
          (Nat.pow_le_pow_right (Nat.le_trans (by decide) hq) hkn)
      exact absurd (le_of_dvd_pos (q ^ k) n hn h) (Nat.not_le.mpr hqk)
  · intro h
    exact dtrans (pow_dvd_of_le q h) (pow_vpSub_dvd q n hq0)

end E213.Meta.Nat.VpSub213
