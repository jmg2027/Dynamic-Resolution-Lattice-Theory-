import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Nat.PolyNatMTactic

/-!
# PrimeSquareFactor — the prime-square factorization arithmetic

The Eisenstein split-prime descent ends with: `p` reducible in `ℤ[ω]` gives `p = d·e`
(non-units), so `p² = ‖d‖²·‖e‖²` with both factors `≥ 2`, forcing `‖d‖² = p`.  The
number-theoretic core is the `ℕ` fact:

  * ★★★ `eq_p_of_mul_eq_psq` — `p` prime, `a·b = p²`, `2 ≤ a`, `2 ≤ b` ⟹ `a = p`.  Both `a`
    and `b` are divisible by `p` (`dvd_prime_pow_cases`), so `a = p·a'`, `b = p·b'`, and
    `p²·(a'b') = p²` forces `a'b' = 1`, hence `a' = 1`, `a = p`.

Built on the `MarkovPrimeFactor` prime-power library.  All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor

open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (dvd_prime_pow_cases)
open E213.Meta.Nat.Gcd213 (mul_eq_one_left)

/-- ★★★ **`a·b = p²` with `a, b ≥ 2` and `p` prime forces `a = p`** (and symmetrically
    `b = p`): the only factorization of `p²` into two factors `≥ 2`. -/
theorem eq_p_of_mul_eq_psq (p a b : Nat) (hp2 : 2 ≤ p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (h : a * b = p ^ 2) : a = p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hane1 : a ≠ 1 := by intro he; rw [he] at ha2; exact absurd ha2 (by decide)
  have hbne1 : b ≠ 1 := by intro he; rw [he] at hb2; exact absurd hb2 (by decide)
  have hpa : p ∣ a := by
    rcases dvd_prime_pow_cases p hp2 hpr 2 a ⟨b, h.symm⟩ with h1 | hp
    · exact absurd h1 hane1
    · exact hp
  have hpb : p ∣ b := by
    rcases dvd_prime_pow_cases p hp2 hpr 2 b ⟨a, by rw [Nat.mul_comm]; exact h.symm⟩
      with h1 | hp
    · exact absurd h1 hbne1
    · exact hp
  obtain ⟨a', ha'⟩ := hpa
  obtain ⟨b', hb'⟩ := hpb
  rw [ha', hb'] at h
  rw [show p ^ 2 = p * p from by rw [Nat.pow_succ, Nat.pow_one]] at h
  rw [show (p * a') * (p * b') = (p * p) * (a' * b') from by ring_nat] at h
  have h1 : (p * p) * (a' * b') = (p * p) * 1 := by rw [Nat.mul_one]; exact h
  have hab1 : a' * b' = 1 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hppos hppos) h1
  have ha'1 : a' = 1 := mul_eq_one_left a' b' hab1
  rw [ha', ha'1, Nat.mul_one]

end E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor
