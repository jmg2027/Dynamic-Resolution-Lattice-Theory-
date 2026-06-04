import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit
import E213.Lib.Math.NumberTheory.ModArith.QRNegOne
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid

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
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int int_dvd_to_nat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit (split_form)
open E213.Tactic.Pow213 (le_of_dvd_pos)

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

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianTwoSquare
