import E213.Lib.Math.NumberTheory.ModArith.NonFixedExists
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# QRNegOne — `−1` is a quadratic residue mod `p` for `p ≡ 1 (mod 4)`

Gaussian Pillar I (disc-`−4` analog of `EisensteinConverse`'s Pillar I): `p` prime,
`p ≡ 1 (mod 4)` ⟹ `∃ x, p ∣ x² + 1`.

Argument (reusing the *generalized* Lagrange-bound non-residue existence):
let `4k = p − 1`.  A non-`(2k)`-fixed element `a` (`a^(2k) ≢ 1`, exists by
`exists_nonfixed_gen` since `2k + 1 ≤ 4k`) gives `Y = a^(2k)` with `Y² = a^(4k) ≡ 1` (FLT) but
`Y ≢ 1`.  So `p ∣ Y²−1 = (Y−1)(Y+1)` and `p ∤ (Y−1)`, whence `p ∣ (Y+1)` (Euclid, `p` prime).
With `x = a^k` (so `x² = a^(2k) = Y`), `p ∣ x² + 1`.

  * ★★★★ `qr_neg_one` — `∃ x, p ∣ x²+1`, the disc-`−4` quadratic-residue input.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.QRNegOne

open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (exists_nonfixed_gen)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
  (dvd_sub_one_of_mod_one mod_one_of_dvd_sub_one pow_add_pure one_le_pow')
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
  (prime_coprime modBezout_gcd_one euclid_of_coprime)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right sub_add_cancel le_sub_of_add_le)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- Divisor-dichotomy primality ⟹ the Bezout-gcd witness FLT needs. -/
private theorem prime_gcd (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ m, 0 < m → m < p → (modBezout m p).1 = 1 := by
  intro m hm0 hmlt
  have hnp : ¬ p ∣ m := fun hpm => absurd (le_of_dvd_pos p m hm0 hpm) (Nat.not_le.mpr hmlt)
  have hco' : gcd213 m p = 1 := by rw [gcd213_comm]; exact prime_coprime p m hpr hnp
  exact modBezout_gcd_one m p hco'

/-- ★★★★ **`−1` is a QR mod a prime `p ≡ 1 (mod 4)`.**  `∃ x, p ∣ x²+1`. -/
theorem qr_neg_one (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 4 = 1) : ∃ x : Nat, p ∣ (x * x + 1) := by
  -- 4k = p - 1
  obtain ⟨k, hp14⟩ : ∃ k, p - 1 = 4 * k := by
    refine ⟨p / 4, ?_⟩
    have hdm := div_add_mod p 4
    rw [hmod] at hdm
    generalize p / 4 = q at hdm
    rw [← hdm, add_sub_cancel_right]
  have hk1 : 1 ≤ k := by
    have hp1 : 1 ≤ p - 1 := le_sub_of_add_le hp
    rw [hp14] at hp1
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hp1; exact absurd hp1 (by decide)
    · exact h0
  have hm1 : 1 ≤ 2 * k := Nat.le_trans hk1 (Nat.le_mul_of_pos_left k (by decide))
  have hlenpre : 2 * k + 1 ≤ p - 1 := by
    rw [hp14]
    have ht : 2 * k + 2 * k = 4 * k := by ring_nat
    calc 2 * k + 1 ≤ 2 * k + 2 * k := Nat.add_le_add_left hm1 (2 * k)
      _ = 4 * k := ht
  -- a non-(2k)-fixed element
  obtain ⟨a, ha1, halt, hanf⟩ := exists_nonfixed_gen p (2 * k) hp hpr hm1 hlenpre
  obtain ⟨Y, hYdef⟩ : ∃ Y, a ^ (2 * k) = Y := ⟨_, rfl⟩
  rw [hYdef] at hanf
  have hY1 : 1 ≤ Y := by rw [← hYdef]; exact one_le_pow' a ha1 (2 * k)
  -- FLT: Y² = a^(4k) ≡ 1
  have hpg := prime_gcd p hpr
  have hflt : a ^ (p - 1) % p = 1 := by
    have h := universal_flt_main a p hp ha1 halt hpg
    rw [Nat.mod_eq_of_lt hp] at h; exact h
  have hYY : a ^ (4 * k) = Y * Y := by
    rw [show 4 * k = (2 * k) + (2 * k) from by ring_nat, pow_add_pure, hYdef]
  rw [hp14, hYY] at hflt
  have hdvdYY : p ∣ Y * Y - 1 := dvd_sub_one_of_mod_one p (Y * Y) hflt
  -- factor Y² − 1 = (Y−1)(Y+1)
  have hsq : ∀ z : Nat, (z + 1) * (z + 1) - 1 = z * (z + 2) := by
    intro z
    have h1 : (z + 1) * (z + 1) = z * (z + 2) + 1 := by ring_nat
    rw [h1, add_sub_cancel_right]
  have hz : Y = (Y - 1) + 1 := (sub_add_cancel hY1).symm
  have hfact : Y * Y - 1 = (Y - 1) * ((Y - 1) + 2) := by
    have hs := hsq (Y - 1); rw [← hz] at hs; exact hs
  have hdvdfact : p ∣ (Y - 1) * ((Y - 1) + 2) := hfact ▸ hdvdYY
  -- p ∤ (Y − 1), so p ∣ (Y + 1) by Euclid
  have hnp : ¬ p ∣ (Y - 1) := fun hd => hanf (mod_one_of_dvd_sub_one p Y hp hY1 hd)
  have hco : gcd213 (Y - 1) p = 1 := by rw [gcd213_comm]; exact prime_coprime p (Y - 1) hpr hnp
  have hp_z2 : p ∣ ((Y - 1) + 2) := euclid_of_coprime (Y - 1) ((Y - 1) + 2) p hp hco hdvdfact
  -- x = a^k, x² = a^(2k) = Y, so x²+1 = (Y−1)+2
  refine ⟨a ^ k, ?_⟩
  have hxx : a ^ k * a ^ k = Y := by
    rw [← pow_add_pure a k k, show k + k = 2 * k from by ring_nat, hYdef]
  rw [hxx]
  have hval : (Y - 1) + 2 = Y + 1 := by rw [show (2 : Nat) = 1 + 1 from rfl, ← Nat.add_assoc, ← hz]
  rw [← hval]; exact hp_z2

end E213.Lib.Math.NumberTheory.ModArith.QRNegOne
