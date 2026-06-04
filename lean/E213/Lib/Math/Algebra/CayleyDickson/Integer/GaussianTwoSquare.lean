import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit
import E213.Lib.Math.NumberTheory.ModArith.QRNegOne
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.PolyIntMTactic

/-!
# GaussianTwoSquare — Fermat's two-square theorem `p ≡ 1 (mod 4) ⟹ p = a² + b²`

The disc-`−4` capstone, assembling the two Gaussian pillars (both ∅-axiom):

  * **Pillar I** (`QRNegOne.qr_neg_one`): `p ≡ 1 (mod 4) ⟹ ∃ x, p ∣ x²+1`.
  * **Pillar II** (`GaussianSplit.split_form`): `p ∣ x²+1 ⟹ p = a²+b²`.

  * ★★★★★ `two_square_of_mod4` — `p` prime, `p ≡ 1 (mod 4)` ⟹ `∃ a b : Int, ↑p = a² + b²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianTwoSquare

open E213.Lib.Math.NumberTheory.ModArith.QRNegOne (qr_neg_one)
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int int_dvd_to_nat dvd_add')
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (mod_one_of_dvd_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit (split_form)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (cases_lt_three)

/-- ★★★★★ **Fermat's two-square theorem.**  A prime `p ≡ 1 (mod 4)` is a sum of two squares:
    `∃ a b : Int, ↑p = a² + b²`.  Pillar I (`−1` a QR) feeds Pillar II (`ℤ[i]` descent). -/
theorem two_square_of_mod4 (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 4 = 1) : ∃ a b : Int, (p : Int) = a * a + b * b := by
  obtain ⟨x, hx⟩ := qr_neg_one p hp hpr hmod
  -- transfer p ∣ x²+1 to ℤ
  have hxcast : ((x * x + 1 : Nat) : Int) = (x : Int) * (x : Int) + 1 := rfl
  have hxint : (p : Int) ∣ ((x : Int) * (x : Int) + 1) := by
    rw [← hxcast]
    exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact hx)
  -- p ∤ 1 in ℤ
  have hp1 : ¬ ((p : Int) ∣ (1 : Int)) := by
    intro hd
    have hle := le_of_dvd_pos p (Int.natAbs (1 : Int)) (by decide) (int_dvd_to_nat p 1 hd)
    rw [show Int.natAbs (1 : Int) = 1 from rfl] at hle
    exact absurd hle (Nat.not_le.mpr hp)
  exact split_form p hp hpr hp1 (x : Int) hxint

/-! ## Necessity (the mod-4 obstruction) and the full iff -/

/-- `2·|r| ≤ 4` ⟹ `r ∈ {−2,−1,0,1,2}` (balanced residues mod 4). -/
theorem int_small4 (r : Int) (h : 2 * r.natAbs ≤ 4) :
    r = -2 ∨ r = -1 ∨ r = 0 ∨ r = 1 ∨ r = 2 := by
  have hle : r.natAbs ≤ 2 := by
    rcases Nat.lt_or_ge r.natAbs 3 with hlt | hge
    · exact Nat.le_of_lt_succ hlt
    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 2 hge) h) (by decide)
  rcases Int.natAbs_eq r with he | he
  · rcases cases_lt_three (Nat.lt_succ_of_le hle) with h0 | h1 | h2
    · right; right; left; rw [he, h0]; decide
    · right; right; right; left; rw [he, h1]; decide
    · right; right; right; right; rw [he, h2]; decide
  · rcases cases_lt_three (Nat.lt_succ_of_le hle) with h0 | h1 | h2
    · right; right; left; rw [he, h0]; decide
    · right; left; rw [he, h1]; decide
    · left; rw [he, h2]; decide

/-- A perfect square is `≡ 0` or `1 (mod 4)`. -/
theorem sq4 (c : Int) : (4 : Int) ∣ (c * c) ∨ (4 : Int) ∣ (c * c - 1) := by
  obtain ⟨q, r, hd, hr⟩ := centered_div_int c 4 (by decide)
  rw [show (4 : Int).natAbs = 4 from rfl] at hr
  have hpack : (4 : Int) ∣ (c * c - r * r) := ⟨4 * q * q + 2 * q * r, by rw [hd]; ring_intZ⟩
  rcases int_small4 r hr with h | h | h | h | h
  · left
    have e : c * c - r * r = c * c - 4 := by rw [h]; ring_intZ
    have hcc : c * c = (c * c - 4) + 4 := by ring_intZ
    rw [hcc]; exact dvd_add' (e ▸ hpack) ⟨1, by ring_intZ⟩
  · right
    have e : c * c - r * r = c * c - 1 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · left
    have e : c * c - r * r = c * c := by rw [h, show (0 : Int) * 0 = 0 from rfl,
      E213.Meta.Int213.Order.sub_zero]
    rw [e] at hpack; exact hpack
  · right
    have e : c * c - r * r = c * c - 1 := by rw [h]; ring_intZ
    rw [e] at hpack; exact hpack
  · left
    have e : c * c - r * r = c * c - 4 := by rw [h]; ring_intZ
    have hcc : c * c = (c * c - 4) + 4 := by ring_intZ
    rw [hcc]; exact dvd_add' (e ▸ hpack) ⟨1, by ring_intZ⟩

/-- `a² + b² ≡ 0, 1`, or `2 (mod 4)` — never `3`. -/
theorem form4_residue (a b : Int) :
    (4 : Int) ∣ (a * a + b * b) ∨ (4 : Int) ∣ (a * a + b * b - 1)
      ∨ (4 : Int) ∣ (a * a + b * b - 2) := by
  rcases sq4 a with ha | ha <;> rcases sq4 b with hb | hb
  · left; exact dvd_add' ha hb
  · right; left
    have e : a * a + b * b - 1 = a * a + (b * b - 1) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; left
    have e : a * a + b * b - 1 = (a * a - 1) + b * b := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; right
    have e : a * a + b * b - 2 = (a * a - 1) + (b * b - 1) := by ring_intZ
    rw [e]; exact dvd_add' ha hb

/-- ★★★★ **Necessity.**  An odd prime `p` of the form `a² + b²` satisfies `p ≡ 1 (mod 4)`.
    Squares avoid `3 mod 4` (`form4_residue`); oddness rules out `0` and `2`. -/
theorem mod4_of_two_square (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hne2 : p ≠ 2) (a b : Int) (hrep : (p : Int) = a * a + b * b) : p % 4 = 1 := by
  have hodd : ¬ 2 ∣ p := by
    intro hd; rcases hpr 2 hd with h | h
    · exact absurd h (by decide)
    · exact hne2 h.symm
  rcases form4_residue a b with h0 | h1 | h2
  · exfalso
    rw [← hrep] at h0
    obtain ⟨c, hc⟩ := h0
    have h2p : (2 : Int) ∣ (p : Int) := ⟨2 * c, by rw [hc]; ring_intZ⟩
    exact hodd (by rw [← Int.natAbs_ofNat p]; exact int_dvd_to_nat 2 (p : Int) h2p)
  · rw [← hrep, ← natCast_sub_one p (Nat.le_of_lt hp)] at h1
    have hnat : 4 ∣ (p - 1) := by
      rw [← Int.natAbs_ofNat (p - 1)]; exact int_dvd_to_nat 4 ((p - 1 : Nat) : Int) h1
    exact mod_one_of_dvd_sub_one 4 p (by decide) (Nat.le_of_lt hp) hnat
  · exfalso
    rw [← hrep] at h2
    obtain ⟨c, hc⟩ := h2
    have hpval : (p : Int) = 4 * c + 2 := by rw [← hc]; ring_intZ
    have h2p : (2 : Int) ∣ (p : Int) := ⟨2 * c + 1, by rw [hpval]; ring_intZ⟩
    exact hodd (by rw [← Int.natAbs_ofNat p]; exact int_dvd_to_nat 2 (p : Int) h2p)

/-- ★★★★★ **Fermat's two-square iff.**  For an odd prime `p`:
    `p ≡ 1 (mod 4) ⟺ ∃ a b : Int, ↑p = a² + b²`. -/
theorem two_square_iff (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hne2 : p ≠ 2) :
    p % 4 = 1 ↔ ∃ a b : Int, (p : Int) = a * a + b * b := by
  constructor
  · intro hmod; exact two_square_of_mod4 p hp hpr hmod
  · rintro ⟨a, b, hrep⟩; exact mod4_of_two_square p hp hpr hne2 a b hrep

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianTwoSquare
