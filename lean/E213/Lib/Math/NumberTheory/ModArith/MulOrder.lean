import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.ModPow213
import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# MulOrder — the multiplicative order mod a prime `p`

`ordModP a p` = the least `k ≥ 1` with `aᵏ ≡ 1 (mod p)`.  For a unit `a` (`1 ≤ a < p`, `p` prime)
it exists by Fermat (`a^(p−1) ≡ 1`, `universal_flt_main`).  The reusable foundation toward
**primitive roots** (`(ℤ/p)*` cyclic) — and thence the Zolotarev nontriviality witness.

  * `pow_ord` — `a^(ordModP a p) % p = 1`.
  * `ord_pos` — `1 ≤ ordModP a p`.
  * `ord_min` — minimality: `1 ≤ j < ord ⟹ aʲ ≢ 1`.
  * ★★★ `ord_dvd` — `aᵏ ≡ 1 ⟹ ord ∣ k` (the division-with-remainder + minimality argument).
  * ★★ `ord_dvd_p_sub_one` — `ord ∣ (p − 1)` (Fermat).

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.MulOrder

open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc modBezout_gcd_one prime_coprime)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right le_sub_of_add_le)
open E213.Meta.Nat.AddMod213 (div_add_mod mod_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure one_le_pow')

/-- Prime ⟹ the modular-Bezout coprimality side-condition Fermat needs. -/
private theorem prime_gcd (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ m, 0 < m → m < p → (modBezout m p).1 = 1 := by
  intro m hm0 hmlt
  have hnp : ¬ p ∣ m := fun hpm => absurd (le_of_dvd_pos p m hm0 hpm) (Nat.not_le.mpr hmlt)
  have hco' : gcd213 m p = 1 := by
    rw [gcd213_comm]; exact prime_coprime p m hpr hnp
  exact modBezout_gcd_one m p hco'

/-- **Fermat's little theorem** (clean form): `a^(p−1) % p = 1` for a prime `p`, unit `1 ≤ a < p`. -/
theorem fermat (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : a ^ (p - 1) % p = 1 := by
  have h := universal_flt_main a p hp ha0 halt (prime_gcd p hpr)
  rwa [Nat.mod_eq_of_lt hp] at h

/-! ## §1 — the order search -/

/-- Search upward from `k` for the least exponent with `aᵏ ≡ 1 (mod p)`. -/
def findOrd (a p : Nat) : Nat → Nat → Option Nat
  | _, 0        => none
  | k, fuel + 1 => if a ^ k % p = 1 then some k else findOrd a p (k + 1) fuel

/-- A found order satisfies the congruence and is `≥` the search start. -/
theorem findOrd_some (a p : Nat) : ∀ (fuel start k : Nat),
    findOrd a p start fuel = some k → a ^ k % p = 1 ∧ start ≤ k
  | 0,        _,     _, h => Option.noConfusion h
  | fuel + 1, start, k, h => by
    rw [findOrd] at h
    by_cases hc : a ^ start % p = 1
    · rw [if_pos hc] at h
      have : start = k := Option.some.inj h
      subst this; exact ⟨hc, Nat.le_refl _⟩
    · rw [if_neg hc] at h
      obtain ⟨h1, h2⟩ := findOrd_some a p fuel (start + 1) k h
      exact ⟨h1, Nat.le_trans (Nat.le_succ start) h2⟩

/-- A found order is minimal: nothing in `[start, k)` satisfies the congruence. -/
theorem findOrd_min (a p : Nat) : ∀ (fuel start k : Nat),
    findOrd a p start fuel = some k → ∀ j, start ≤ j → j < k → a ^ j % p ≠ 1
  | 0,        _,     _, h => Option.noConfusion h
  | fuel + 1, start, k, h => by
    rw [findOrd] at h
    by_cases hc : a ^ start % p = 1
    · rw [if_pos hc] at h
      have hsk : start = k := Option.some.inj h
      intro j hsj hjk
      rw [← hsk] at hjk
      exact absurd hjk (Nat.not_lt.mpr hsj)
    · rw [if_neg hc] at h
      intro j hsj hjk
      rcases Nat.lt_or_eq_of_le hsj with hlt | heq
      · exact findOrd_min a p fuel (start + 1) k h j hlt hjk
      · rw [← heq]; exact hc

/-- The search succeeds within `fuel` whenever some exponent in `[start, start+fuel)` works. -/
theorem findOrd_found (a p : Nat) : ∀ (fuel start t : Nat),
    start ≤ t → t < start + fuel → a ^ t % p = 1 → ∃ k, findOrd a p start fuel = some k
  | 0,        _,     t, hst, hlt, _  => by
    rw [Nat.add_zero] at hlt; exact absurd hlt (Nat.not_lt.mpr hst)
  | fuel + 1, start, t, hst, hlt, ht => by
    rw [findOrd]
    by_cases hc : a ^ start % p = 1
    · exact ⟨start, by rw [if_pos hc]⟩
    · rw [if_neg hc]
      have hst' : start + 1 ≤ t := by
        rcases Nat.lt_or_eq_of_le hst with hlt2 | heq
        · exact hlt2
        · exact absurd (heq ▸ ht) hc
      exact findOrd_found a p fuel (start + 1) t hst' (by
        rw [Nat.succ_add]; exact hlt) ht

/-! ## §2 — `ordModP` and its laws -/

/-- The multiplicative order of `a` mod `p` (least positive exponent with `aᵏ ≡ 1`); `0` if none. -/
def ordModP (a p : Nat) : Nat := (findOrd a p 1 p).getD 0

/-- For a prime `p` and unit `a`, the search succeeds (Fermat provides the exponent `p−1`). -/
theorem ord_found (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : ∃ k, findOrd a p 1 p = some k := by
  have hp1 : 1 ≤ p - 1 := le_sub_of_add_le hp
  have hlt : p - 1 < 1 + p :=
    Nat.lt_of_le_of_lt (Nat.sub_le p 1) (by rw [Nat.add_comm]; exact Nat.lt_succ_self p)
  exact findOrd_found a p p 1 (p - 1) hp1 hlt (fermat a p hp hpr ha0 halt)

theorem pow_ord (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : a ^ (ordModP a p) % p = 1 := by
  obtain ⟨k, hk⟩ := ord_found a p hp hpr ha0 halt
  have hord : ordModP a p = k := congrArg (·.getD 0) hk
  rw [hord]; exact (findOrd_some a p p 1 k hk).1

theorem ord_pos (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : 1 ≤ ordModP a p := by
  obtain ⟨k, hk⟩ := ord_found a p hp hpr ha0 halt
  have hord : ordModP a p = k := congrArg (·.getD 0) hk
  rw [hord]; exact (findOrd_some a p p 1 k hk).2

/-- Minimality: no positive exponent below the order satisfies the congruence. -/
theorem ord_min (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : ∀ j, 1 ≤ j → j < ordModP a p → a ^ j % p ≠ 1 := by
  obtain ⟨k, hk⟩ := ord_found a p hp hpr ha0 halt
  have hord : ordModP a p = k := congrArg (·.getD 0) hk
  rw [hord]; exact findOrd_min a p p 1 k hk

/-! ## §3 — `aᵏ ≡ 1 ⟹ ord ∣ k` -/

/-- `a^(ord·q + r) ≡ aʳ (mod p)` — the `a^ord ≡ 1` collapse. -/
theorem pow_split_eq (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) (q r : Nat) :
    a ^ (ordModP a p * q + r) % p = a ^ r % p := by
  rw [pow_add_pure a (ordModP a p * q) r, pow_mul_loc a (ordModP a p) q]
  -- ((a^ord)^q * a^r) % p, with (a^ord)^q ≡ 1
  have hbase : (a ^ ordModP a p) ^ q % p = 1 := by
    rw [pow_mod_base (a ^ ordModP a p) p q, pow_ord a p hp hpr ha0 halt]
    show 1 ^ q % p = 1
    rw [Nat.one_pow]; exact Nat.mod_eq_of_lt hp
  calc (a ^ ordModP a p) ^ q * a ^ r % p
      = ((a ^ ordModP a p) ^ q % p * (a ^ r % p)) % p := mul_mod_pure _ _ p
    _ = (1 * (a ^ r % p)) % p := by rw [hbase]
    _ = a ^ r % p := by rw [Nat.one_mul, mod_mod]

/-- ★★★ **`aᵏ ≡ 1 ⟹ ord ∣ k`** — the order divides every exponent that fixes `a`.  By
    `k = ord·q + r` (`r < ord`): `aᵏ ≡ aʳ`, so `aʳ ≡ 1` with `r < ord` forces `r = 0` (minimality). -/
theorem ord_dvd (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) (k : Nat) (hk : a ^ k % p = 1) : ordModP a p ∣ k := by
  have hop : 1 ≤ ordModP a p := ord_pos a p hp hpr ha0 halt
  have hdm : ordModP a p * (k / ordModP a p) + k % ordModP a p = k := div_add_mod k (ordModP a p)
  have hr : a ^ (k % ordModP a p) % p = 1 := by
    have h := pow_split_eq a p hp hpr ha0 halt (k / ordModP a p) (k % ordModP a p)
    rw [hdm] at h; rw [← h]; exact hk
  -- r = k % ord < ord, and a^r ≡ 1 ⟹ r = 0 (minimality)
  have hrlt : k % ordModP a p < ordModP a p := Nat.mod_lt k (Nat.lt_of_lt_of_le Nat.zero_lt_one hop)
  have hr0 : k % ordModP a p = 0 := by
    rcases Nat.eq_zero_or_pos (k % ordModP a p) with h0 | hpos
    · exact h0
    · exact absurd hr (ord_min a p hp hpr ha0 halt (k % ordModP a p) hpos hrlt)
  have hk_eq : ordModP a p * (k / ordModP a p) = k := by
    rw [hr0, Nat.add_zero] at hdm; exact hdm
  exact ⟨k / ordModP a p, hk_eq.symm⟩

/-- ★★ **`ord ∣ (p − 1)`** — the order divides the group order (Fermat). -/
theorem ord_dvd_p_sub_one (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : ordModP a p ∣ (p - 1) :=
  ord_dvd a p hp hpr ha0 halt (p - 1) (fermat a p hp hpr ha0 halt)

end E213.Lib.Math.NumberTheory.ModArith.MulOrder
