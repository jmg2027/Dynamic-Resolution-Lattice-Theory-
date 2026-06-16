import E213.Lib.Math.NumberTheory.ModArith.SqPlusOneFrame
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.PrimesThreeModFour
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Inert-prime obstruction for sums of two squares (∅-axiom)

A prime `q ≡ 3 (mod 4)` is **inert** for sums of two squares:
`q ∣ a² + b² ⟹ q ∣ a ∧ q ∣ b`.

The forcing fact is that `−1` is a quadratic **non-residue** mod `q ≡ 3 mod 4`
(`neg_one_nonresidue_three_mod4`, the contrapositive of `SqPlusOneFrame.sq_plus_one_dvd_iff`).
If `q ∤ b`, the inverse `c` of `b` mod `q` turns `a² ≡ −b²` into `(a·c)² ≡ −1`, contradicting
non-residue.  Hence `q ∣ b`, then `q ∣ a²` and Euclid give `q ∣ a`.
-/

namespace E213.Lib.Math.NumberTheory.InertPrimeThreeMod4

open E213.Lib.Math.NumberTheory.ModArith.SqPlusOneFrame (sq_plus_one_dvd_iff)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
  (inverse_of_coprime prime_coprime dvd_mul_right_loc)
open E213.Lib.Math.NumberTheory.PrimesThreeModFour (mod4_three_odd)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.AddMod213 (add_mod_gen dvd_of_mod_eq_zero)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.Gcd213 (gcd213_comm dvd_sub_213)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right mul_mod_right)
open E213.Lib.Math.NumberTheory.FourSquareSeed (mod_zero_of_dvd)
open E213.Lib.Math.NumberTheory.PerfectNumbers (prime_of_bounded)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)

/-! ## §1 — `−1` is a non-residue mod `q ≡ 3 (mod 4)` -/

/-- ★★★★ **`−1` is a quadratic non-residue mod a prime `q ≡ 3 (mod 4)`.**  No `x` has
    `q ∣ x² + 1` — the disc-`−4` obstruction.  Contrapositive of `sq_plus_one_dvd_iff`
    (`(∃x, q∣x²+1) ↔ q%4=1`): `q%4=3 ≠ 1`. -/
theorem neg_one_nonresidue_three_mod4 (q : Nat) (hq : 1 < q)
    (hpr : ∀ d, d ∣ q → d = 1 ∨ d = q) (hmod : q % 4 = 3) :
    ¬ ∃ x : Nat, q ∣ (x * x + 1) := by
  intro hex
  have hodd : q % 2 = 1 := mod4_three_odd hmod
  have h1 : q % 4 = 1 := (sq_plus_one_dvd_iff q hq hpr hodd).mp hex
  rw [hmod] at h1
  exact absurd h1 (by decide)

/-! ## §2 — the inert-prime obstruction -/

/-- Algebraic core: `(a² + b²)·c² = (a·c)² + (b·c)²`. -/
private theorem sum_sq_mul (a b c : Nat) :
    (a * a + b * b) * (c * c) = (a * c) * (a * c) + (b * c) * (b * c) := by ring_nat

/-- If `q ∣ a² + b²` and `q ∤ b` (q prime), then `q ∣ (a·c)² + 1` where `c` inverts `b` mod `q`.
    Multiply the divisibility by `c²` and replace `(b·c)² ≡ 1`. -/
private theorem root_of_not_dvd (q a b : Nat) (hq : 1 < q)
    (hpr : ∀ d, d ∣ q → d = 1 ∨ d = q) (hdvd : q ∣ (a * a + b * b)) (hnb : ¬ q ∣ b) :
    ∃ x : Nat, q ∣ (x * x + 1) := by
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hq)
  -- inverse c of b mod q
  have hco : gcd213 b q = 1 := by rw [gcd213_comm]; exact prime_coprime q b hpr hnb
  obtain ⟨c, hcdef⟩ : ∃ c, (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout b q).2 = c :=
    ⟨_, rfl⟩
  have hinv : (b * c) % q = 1 % q := by rw [← hcdef]; exact inverse_of_coprime b q hqpos hco
  have hinv' : (b * c) % q = 1 := by rw [hinv, Nat.mod_eq_of_lt hq]
  -- q ∣ (a*c)² + (b*c)²
  have hmul : q ∣ ((a * c) * (a * c) + (b * c) * (b * c)) := by
    have h1 : q ∣ ((a * a + b * b) * (c * c)) := by
      obtain ⟨k, hk⟩ := hdvd
      exact ⟨k * (c * c), by rw [hk]; ring_nat⟩
    rwa [sum_sq_mul a b c] at h1
  -- (b*c)*(b*c) ≡ 1 (mod q)
  have hbc1 : ((b * c) * (b * c)) % q = 1 := by
    rw [mul_mod_pure (b * c) (b * c) q, hinv', Nat.mul_one, Nat.mod_eq_of_lt hq]
  -- ((a*c)² + 1) % q = ((a*c)² + (b*c)²) % q = 0
  refine ⟨a * c, ?_⟩
  apply dvd_of_mod_eq_zero
  have hstep : ((a * c) * (a * c) + 1) % q = ((a * c) * (a * c) + (b * c) * (b * c)) % q := by
    rw [add_mod_gen ((a * c) * (a * c)) 1 q, add_mod_gen ((a * c) * (a * c)) ((b * c) * (b * c)) q,
        hbc1, Nat.mod_eq_of_lt hq]
  rw [hstep]
  obtain ⟨w, hw⟩ := hmul
  rw [hw]; exact mul_mod_right q w

/-- ★★★★★ **The inert-prime obstruction.**  A prime `q ≡ 3 (mod 4)` dividing `a² + b²`
    divides both `a` and `b`. -/
theorem inert_three_mod4 (q a b : Nat) (hq : 1 < q)
    (hpr : ∀ d, d ∣ q → d = 1 ∨ d = q) (hmod : q % 4 = 3)
    (hdvd : q ∣ (a * a + b * b)) :
    q ∣ a ∧ q ∣ b := by
  -- q ∣ b: else a root of −1 exists, contradicting non-residue
  have hb : q ∣ b := by
    rcases Nat.eq_zero_or_pos (b % q) with h0 | hpos
    · exact E213.Lib.Math.NumberTheory.FourSquareSeed.dvd_of_mod_zero b q h0
    · exfalso
      have hnb : ¬ q ∣ b := fun hd => Nat.lt_irrefl 0 (mod_zero_of_dvd b q hd ▸ hpos)
      exact neg_one_nonresidue_three_mod4 q hq hpr hmod (root_of_not_dvd q a b hq hpr hdvd hnb)
  -- q ∣ a*a: q ∣ a²+b² and q ∣ b² (= b*b)
  have hbb : q ∣ (b * b) := dvd_mul_right_loc q b b hb
  have hle : b * b ≤ a * a + b * b := Nat.le_add_left (b * b) (a * a)
  have haa : q ∣ (a * a) := by
    have hsub := dvd_sub_213 (b * b) (a * a + b * b) q hle hbb hdvd
    have heq : (a * a + b * b) - (b * b) = a * a := add_sub_cancel_right (a * a) (b * b)
    rwa [heq] at hsub
  have ha : q ∣ a := by
    rcases nat_prime_dvd_mul q hq hpr a a haa with h | h
    · exact h
    · exact h
  exact ⟨ha, hb⟩

/-! ## §3 — descent step: `q ∣ a²+b² ⟹ q² ∣ a²+b²` (the heart of the odd-power obstruction)

The inert-prime lemma says `q ∣ a` and `q ∣ b`, so `q² ∣ a²` and `q² ∣ b²`, hence
`q² ∣ a²+b²`.  Iterating this is exactly the descent that forces the `q`-adic valuation of any
sum of two squares to be **even** at every prime `q ≡ 3 (mod 4)` — the "only if" direction. -/

/-- ★★★★ **Descent step.**  For a prime `q ≡ 3 (mod 4)`: `q ∣ a²+b² ⟹ q² ∣ a²+b²`.
    (`q∣a, q∣b` from `inert_three_mod4`, then `q²∣a², q²∣b²`.) -/
theorem qsq_dvd_of_dvd_three_mod4 (q a b : Nat) (hq : 1 < q)
    (hpr : ∀ d, d ∣ q → d = 1 ∨ d = q) (hmod : q % 4 = 3)
    (hdvd : q ∣ (a * a + b * b)) :
    (q * q) ∣ (a * a + b * b) := by
  obtain ⟨ha, hb⟩ := inert_three_mod4 q a b hq hpr hmod hdvd
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  exact ⟨s * s + t * t, by rw [hs, ht]; ring_nat⟩

/-! ## §4 — small-prime smokes (closed bounded checks of the non-residue lemma) -/

private theorem prime3' : Prime213 3 := prime_of_bounded (by decide) (B := 2) (by decide) (by decide)
private theorem prime7' : Prime213 7 := prime_of_bounded (by decide) (B := 3) (by decide) (by decide)
private theorem prime11' : Prime213 11 := prime_of_bounded (by decide) (B := 4) (by decide) (by decide)

/-- `3 ≡ 3 (mod 4)` is inert: `3 ∣ a²+b² ⟹ 3∣a ∧ 3∣b` (instance of `inert_three_mod4`). -/
theorem inert_three (a b : Nat) (hdvd : 3 ∣ (a * a + b * b)) : 3 ∣ a ∧ 3 ∣ b :=
  inert_three_mod4 3 a b (by decide) prime3'.2 (by decide) hdvd

/-- `7 ≡ 3 (mod 4)` is inert. -/
theorem inert_seven (a b : Nat) (hdvd : 7 ∣ (a * a + b * b)) : 7 ∣ a ∧ 7 ∣ b :=
  inert_three_mod4 7 a b (by decide) prime7'.2 (by decide) hdvd

/-- `11 ≡ 3 (mod 4)` is inert. -/
theorem inert_eleven (a b : Nat) (hdvd : 11 ∣ (a * a + b * b)) : 11 ∣ a ∧ 11 ∣ b :=
  inert_three_mod4 11 a b (by decide) prime11'.2 (by decide) hdvd

/-- `−1` is a non-residue mod `7`: no `x` has `7 ∣ x²+1` (instance). -/
theorem nonresidue_seven : ¬ ∃ x : Nat, 7 ∣ (x * x + 1) :=
  neg_one_nonresidue_three_mod4 7 (by decide) prime7'.2 (by decide)

end E213.Lib.Math.NumberTheory.InertPrimeThreeMod4
