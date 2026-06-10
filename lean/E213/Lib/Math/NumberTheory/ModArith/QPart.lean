import E213.Meta.Nat.Valuation
import E213.Lib.Math.NumberTheory.Lcm213
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Nat.PolyNatMTactic

/-!
# QPart — the `q`-part `q^(vp q n)` and its coprimality (marathon brick 4b-ii)

  * `qpart q n := q^(vp q n)`, with `qpart_dvd` (`∣ n`).
  * ★ `q_not_dvd_quot` — `q ∤ (n / qpart q n)` (the `q`-free complement).
  * `gcd_eq_of_dvd` — `b ∣ a ⟹ gcd a b = b`.
  * ★ `gcd_qpow_qfree` — `gcd(qᵉ, B) = 1` when `q` is prime and `q ∤ B`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.QPart

open E213.Meta.Nat.Valuation (vp pow_vp_dvd vp_not_dvd_succ drefl dtrans)
open E213.Lib.Math.NumberTheory.Lcm213 (mul_div_cancel_of_dvd)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest dvd_antisymm_213 mul_assoc_213)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (dvd_prime_pow_cases)
open E213.Tactic.NatHelper (gcd213)

/-- The `q`-part of `n`: `q^(vp q n)`. -/
def qpart (q n : Nat) : Nat := q ^ (vp q n)

theorem qpart_dvd (q n : Nat) : qpart q n ∣ n := pow_vp_dvd q n

theorem qpart_pos (q n : Nat) (hq : 2 ≤ q) : 0 < qpart q n :=
  Nat.pos_pow_of_pos (vp q n) (Nat.lt_of_lt_of_le (by decide) hq)

/-- `b ∣ a ⟹ gcd a b = b`. -/
theorem gcd_eq_of_dvd {a b : Nat} (h : b ∣ a) : gcd213 a b = b :=
  dvd_antisymm_213 _ _ (gcd213_dvd_right a b) (gcd213_greatest a b b h (drefl b))

/-- ★ **`q ∤ (n / qpart q n)`** — the `q`-free complement.  Else `q^(vp+1) ∣ n`, contradicting
    `vp_not_dvd_succ`. -/
theorem q_not_dvd_quot (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) : ¬ q ∣ (n / qpart q n) := by
  intro hdvd
  obtain ⟨s, hs⟩ := hdvd   -- n / qpart q n = q * s
  -- n = qpart · (q·s)  (no `n`-rewrite: only the `q·s` subterm changes)
  have hn_eq : n = qpart q n * (q * s) := by
    rw [← hs]; exact (mul_div_cancel_of_dvd (qpart q n) n (qpart_pos q n hq) (qpart_dvd q n)).symm
  -- qpart · (q·s) = q^(vp+1)·s  (no `n` at all)
  have hkey : qpart q n * (q * s) = q ^ (vp q n + 1) * s := by
    rw [show qpart q n = q ^ vp q n from rfl, Nat.pow_succ]
    exact (mul_assoc_213 _ _ _).symm
  exact vp_not_dvd_succ q n hq hn ⟨s, hn_eq.trans hkey⟩

/-- ★ **`gcd(qᵉ, B) = 1`** when `q` is prime and `q ∤ B`.  A divisor of `qᵉ` is `1` or divisible
    by `q` (`dvd_prime_pow_cases`); the latter forces `q ∣ B`. -/
theorem gcd_qpow_qfree (q e B : Nat) (hq : 2 ≤ q) (hpr : ∀ d, d ∣ q → d = 1 ∨ d = q)
    (hqB : ¬ q ∣ B) : gcd213 (q ^ e) B = 1 := by
  rcases dvd_prime_pow_cases q hq hpr e (gcd213 (q ^ e) B) (gcd213_dvd_left (q ^ e) B) with h1 | hqg
  · exact h1
  · exact absurd (dtrans hqg (gcd213_dvd_right (q ^ e) B)) hqB

end E213.Lib.Math.NumberTheory.ModArith.QPart
