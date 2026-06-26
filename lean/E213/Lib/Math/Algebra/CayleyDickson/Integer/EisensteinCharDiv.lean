import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Meta.Nat.MulMod213

/-!
# The cubic character division identity — `χ_ω(b)·χ̄_ω(c) = χ_ω((b·c⁻¹) mod p)` (∅-axiom)

For units `b, c`, the character of a ratio:

  `χ_ω(b) · conj χ_ω(c) = χ_ω((b · aInv c p) mod p)`   (`chiOmega_div`),

i.e. `χ(b)·χ̄(c) = χ(b/c)`.  `conj χ_ω(c) = χ_ω(c⁻¹)` (both are the `μ₃`-inverse of `χ_ω(c)`, by left
cancellation `mul_left_cancel_zomega` on `χ_ω(c)·χ_ω(c⁻¹) = 1 = χ_ω(c)·conj χ_ω(c)`), then
`χ_ω(b)·χ_ω(c⁻¹) = χ_ω(b·c⁻¹)` (`chiOmega_mul`).  This is the per-term identity behind the Gauss-sum
off-diagonal `C = −1` (`χ(j+1)χ̄(j)=χ(1+j⁻¹)`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
  (chiOmega chiOmega_mul_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex (chiOmega_ne_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (mul_left_cancel_zomega)
open E213.Lib.Math.NumberTheory.EulerTheorem (aInv aInv_spec)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.MulMod213 (mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (add_mod_left)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)

/-- ★★ **`χ_ω(1) = 1`** (for `1 < p`): `1 % p = 1 ≠ 0` and `cubicChar(1) = 1^m % p = 1`. -/
theorem chiOmega_one {p m x : Nat} (hp : 1 < p) : chiOmega p m x 1 = ofInt 1 := by
  have hne : ¬ (1 : Nat) % p = 0 := by rw [Nat.mod_eq_of_lt hp]; decide
  have hc1 : cubicChar p m 1 = 1 := by
    show 1 ^ m % p = 1
    rw [Nat.one_pow, Nat.mod_eq_of_lt hp]
  unfold chiOmega
  rw [if_neg hne, if_pos hc1]

/-- `0 < aInv c p % p` for a unit `c` (else `(c·0)%p = 0 ≠ 1`). -/
theorem aInv_mod_pos {c p : Nat} (hp : 1 < p) (hc : gcd213 c p = 1) : 0 < aInv c p % p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  rcases Nat.eq_zero_or_pos (aInv c p % p) with h0 | h
  · exfalso
    have hs : (c * (aInv c p % p)) % p = 1 % p := by
      rw [← mul_mod_right_pure c (aInv c p) p]; exact aInv_spec hppos hc
    rw [h0, Nat.mul_zero, Nat.mod_eq_of_lt hppos, Nat.mod_eq_of_lt hp] at hs
    exact absurd hs (by decide)
  · exact h

/-- ★★★★ **The character division identity** — `χ_ω(b)·conj χ_ω(c) = χ_ω((b·aInv c p) % p)` for units
    `b, c`.  `conj χ_ω(c) = χ_ω(c⁻¹)` by left cancellation, then `chiOmega_mul`.  ∅-axiom. -/
theorem chiOmega_div {d : ZOmega} {p m x b c : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hb1 : 0 < b) (hblt : b < p) (hc1 : 0 < c) (hclt : c < p) (hcc : gcd213 c p = 1) :
    chiOmega p m x b * conj (chiOmega p m x c) = chiOmega p m x ((b * aInv c p) % p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hcIpos : 0 < aInv c p % p := aInv_mod_pos hp hcc
  have hcIlt : aInv c p % p < p := Nat.mod_lt _ hppos
  -- (c·c⁻¹) mod p = 1
  have hcci : (c * (aInv c p % p)) % p = 1 := by
    rw [← mul_mod_right_pure c (aInv c p) p, aInv_spec hppos hcc, Nat.mod_eq_of_lt hp]
  -- χ_ω(c)·χ_ω(c⁻¹) = 1
  have hprod : chiOmega p m x c * chiOmega p m x (aInv c p % p) = ofInt 1 := by
    rw [chiOmega_mul hp hp3 hpr h3m hdn hω hx hc1 hclt hcIpos hcIlt, hcci, chiOmega_one hp]
  -- conj χ_ω(c) = χ_ω(c⁻¹)  (both the μ₃-inverse of χ_ω(c))
  have hinv : chiOmega p m x (aInv c p % p) = conj (chiOmega p m x c) :=
    mul_left_cancel_zomega (chiOmega_ne_zero p m x c hc1 hclt)
      (hprod.trans (chiOmega_mul_conj p m x c (chiOmega_ne_zero p m x c hc1 hclt)).symm)
  -- assemble:  χ_ω(b)·conj χ_ω(c) = χ_ω(b)·χ_ω(c⁻¹) = χ_ω((b·c⁻¹)%p)
  rw [← hinv, chiOmega_mul hp hp3 hpr h3m hdn hω hx hb1 hblt hcIpos hcIlt,
      ← mul_mod_right_pure b (aInv c p) p]

/-- ★★ **`(v+1)·w ≡ 1 + w (mod p)`** when `v·w ≡ 1` — the ratio `(v+1)/v = 1 + 1/v` at the index
    level.  `(v+1)·w = v·w + w ≡ 1 + w`.  The per-term step turning `χ_ω(u/(u−1))` into
    `χ_ω(1 + (u−1)⁻¹)` for the off-diagonal `C = −1`.  ∅-axiom. -/
theorem mul_succ_inv {v w p : Nat} (hp : 0 < p) (h : (v * w) % p = 1 % p) :
    ((v + 1) * w) % p = (1 + w) % p := by
  rw [Nat.succ_mul, add_mod_left hp (v * w) w, h, ← add_mod_left hp 1 w]

/-- ★★★★ **The ratio character term** — for `2 ≤ u < p` (`u−1` a unit), `χ_ω(u)·χ̄_ω((u−1)%p) =
    χ_ω((1 + (u−1)⁻¹) % p)`, i.e. `χ(u/(u−1)) = χ(1 + 1/(u−1))`.  `chiOmega_div` gives `χ_ω(u/(u−1))`,
    then `mul_succ_inv` rewrites the index `u·(u−1)⁻¹ = 1 + (u−1)⁻¹`.  The off-diagonal `C = −1`
    per-term, ready for the `(u−1)⁻¹`-inversion + `1+·`-shift reindex.  ∅-axiom. -/
theorem chiOmega_ratio_term {d : ZOmega} {p m x u : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hu : 2 ≤ u) (hult : u < p) (hcop : gcd213 (u - 1) p = 1) :
    chiOmega p m x u * conj (chiOmega p m x ((u - 1) % p))
      = chiOmega p m x ((1 + aInv ((u - 1) % p) p) % p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hu1le : 1 ≤ u := Nat.le_trans (by decide) hu
  have hu1lt : u - 1 < p := Nat.lt_of_le_of_lt (Nat.sub_le u 1) hult
  have hu1mod : (u - 1) % p = u - 1 := Nat.mod_eq_of_lt hu1lt
  have hu1pos : 0 < (u - 1) % p := by
    rw [hu1mod]; exact Nat.lt_of_lt_of_le (by decide) (Nat.sub_le_sub_right hu 1)
  have hu0 : 0 < u := Nat.lt_of_lt_of_le (by decide) hu
  have hcop' : gcd213 ((u - 1) % p) p = 1 := by rw [hu1mod]; exact hcop
  rw [chiOmega_div hp hp3 hpr h3m hdn hω hx hu0 hult hu1pos (Nat.mod_lt _ hppos) hcop']
  congr 1
  have hvw : ((u - 1) * aInv ((u - 1) % p) p) % p = 1 % p := by
    rw [hu1mod]; exact aInv_spec hppos hcop
  have hms := mul_succ_inv hppos hvw
  rwa [nat_sub_add_cancel hu1le] at hms
