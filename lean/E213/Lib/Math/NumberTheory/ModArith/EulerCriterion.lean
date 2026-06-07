import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.ModPow213
import E213.Meta.Tactic.Pow213

/-!
# EulerCriterion — Euler's criterion, the `±1` dichotomy

For an odd prime `p` and a residue `a` coprime to `p`, the half-power `a^((p−1)/2)` is a
square root of `1` mod `p` (its square is `a^(p−1) ≡ 1` by Fermat's little theorem), so it is
`≡ ±1`.  Stated divisibility-first (the carrier reading, no `mod`):

  * ★★★★ `euler_dichotomy` — `p ∣ (aᵐ − 1) ∨ p ∣ (aᵐ + 1)` where `2m = p − 1`.

The argument is the disc-`−4` `QRNegOne` shape transposed to a general base: `Y = aᵐ`,
`Y·Y = a^(p−1) ≡ 1` (FLT), factor `Y²−1 = (Y−1)(Y+1)`, then Euclid splits the prime across the
two factors.  The exponent is carried as a hypothesis `2m = p − 1` (the odd-prime witness),
mirroring `exists_nonfixed`'s `3m = p − 1`, so no division enters.

The half (`a` a quadratic residue ⟹ the `+1` branch) and the converse (the root-count
collapse, via `RootBound.eval_zero`) build on this dichotomy.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.EulerCriterion

open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
  (dvd_sub_one_of_mod_one pow_add_pure one_le_pow')
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
  (prime_coprime modBezout_gcd_one pow_mul_loc)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right sub_add_cancel)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- Divisor-dichotomy primality ⟹ the Bezout-gcd witness FLT needs (the `QRNegOne.prime_gcd`
    helper, re-derived: a residue `0 < m < p` is coprime to a prime `p`). -/
private theorem prime_gcd (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ m, 0 < m → m < p → (modBezout m p).1 = 1 := by
  intro m hm0 hmlt
  have hnp : ¬ p ∣ m := fun hpm => absurd (le_of_dvd_pos p m hm0 hpm) (Nat.not_le.mpr hmlt)
  have hco' : gcd213 m p = 1 := by rw [gcd213_comm]; exact prime_coprime p m hpr hnp
  exact modBezout_gcd_one m p hco'

/-- ★★★★ **Euler's criterion — the `±1` dichotomy.**  For a prime `p`, an exponent `m` with
    `2m = p − 1` (so `p` is odd), and a residue `1 ≤ a < p`, the half-power `aᵐ` satisfies
    `p ∣ (aᵐ − 1) ∨ p ∣ (aᵐ + 1)` — i.e. `aᵐ ≡ ±1 (mod p)`.  `Y = aᵐ` has `Y² = a^(p−1) ≡ 1`
    (FLT); `p ∣ Y²−1 = (Y−1)(Y+1)` splits by Euclid. -/
theorem euler_dichotomy (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hpm : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    p ∣ (a ^ m - 1) ∨ p ∣ (a ^ m + 1) := by
  have hpg := prime_gcd p hpr
  obtain ⟨Y, hYdef⟩ : ∃ Y, a ^ m = Y := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [← hYdef]; exact one_le_pow' a ha1 m
  -- FLT: Y·Y = a^(p−1) ≡ 1
  have hflt : a ^ (p - 1) % p = 1 := by
    have h := universal_flt_main a p hp ha1 halt hpg
    rw [Nat.mod_eq_of_lt hp] at h; exact h
  have hYY : a ^ (p - 1) = Y * Y := by
    rw [← hpm, show 2 * m = m + m from by ring_nat, pow_add_pure a m m, hYdef]
  rw [hYY] at hflt
  have hdvdYY : p ∣ Y * Y - 1 := dvd_sub_one_of_mod_one p (Y * Y) hflt
  -- factor Y² − 1 = (Y−1)·((Y−1)+2)
  have hsq : ∀ z : Nat, (z + 1) * (z + 1) - 1 = z * (z + 2) := by
    intro z
    have h1 : (z + 1) * (z + 1) = z * (z + 2) + 1 := by ring_nat
    rw [h1, add_sub_cancel_right]
  have hz : Y = (Y - 1) + 1 := (sub_add_cancel hY1).symm
  have hfact : Y * Y - 1 = (Y - 1) * ((Y - 1) + 2) := by
    have hs := hsq (Y - 1); rw [← hz] at hs; exact hs
  have hdvdfact : p ∣ (Y - 1) * ((Y - 1) + 2) := hfact ▸ hdvdYY
  have hval : (Y - 1) + 2 = Y + 1 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, ← Nat.add_assoc, ← hz]
  -- split the prime across the two factors (disjunctive Euclid)
  rcases nat_prime_dvd_mul p hp hpr (Y - 1) ((Y - 1) + 2) hdvdfact with hd | hd
  · left; rw [hYdef]; exact hd
  · right; rw [hYdef, ← hval]; exact hd

/-- ★★★★ **Euler's criterion — the residue direction.**  If `a` is a quadratic residue mod `p`
    (`x² ≡ a` for some unit `1 ≤ x < p`), then `aᵐ ≡ 1 (mod p)` (the `+1` branch of the
    dichotomy): `aᵐ ≡ (x²)ᵐ = x^(2m) = x^(p−1) ≡ 1` by Fermat's little theorem. -/
theorem euler_qr_pow_one (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hpm : 2 * m = p - 1) (x : Nat) (hx1 : 1 ≤ x) (hxlt : x < p) (hx2 : x ^ 2 % p = a) :
    p ∣ (a ^ m - 1) := by
  have hpg := prime_gcd p hpr
  have hflt : a ^ m % p = 1 := by
    rw [← hx2, ← pow_mod_base (x ^ 2) p m, ← pow_mul_loc x 2 m, hpm]
    have h := universal_flt_main x p hp hx1 hxlt hpg
    rwa [Nat.mod_eq_of_lt hp] at h
  exact dvd_sub_one_of_mod_one p (a ^ m) hflt

end E213.Lib.Math.NumberTheory.ModArith.EulerCriterion
