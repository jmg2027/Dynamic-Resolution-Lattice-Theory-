import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum

/-!
# The shifted Gauss-sum per-term identity — `χ_ω((j+k)%p)·χ̄_ω(j) = χ_ω(1+k·j⁻¹)` (∅-axiom, A3 / route b)

The summand of the off-diagonal coefficient `(g⋆ḡ)(k) = Σ_{j<p} χ_ω((j+k)%p)·χ̄_ω(j)`
(`EisensteinGaussShift.gauss_offdiag_shift`), for a **unit** `j`:

  `χ_ω((j+k)%p) · conj χ_ω(j) = χ_ω((1 + (k · (aInv j p % p)) % p) % p)`   (`chiOmega_shift_term`),

i.e. `χ((j+k)/j) = χ(1 + k/j)`.  Two cases on the numerator `(j+k)%p`:
  * `(j+k)%p ≠ 0` (a unit): `chiOmega_div` gives `χ(((j+k)·j⁻¹)%p)`, and `(j+k)·j⁻¹ = j·j⁻¹+k·j⁻¹ ≡
    1+k·j⁻¹` (the index algebra `(1+k·j⁻¹) ≡ (j·j⁻¹+k·j⁻¹) = (j+k)·j⁻¹`).
  * `(j+k)%p = 0` (the **wrap** `j=p−k`): the left side is `χ_ω(0)·… = 0`, and the **same** index
    algebra forces the target index `(1+k·j⁻¹)%p = ((j+k)·j⁻¹)%p = 0`, so the right side is `χ_ω(0)=0`.

The single per-term brick the inversion + multiplication reindexes act on to give the off-diagonal `−1`.
∅-axiom.  (A3 route b.)
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinShiftTerm

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv (chiOmega_div)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.NumberTheory.EulerTheorem (aInv aInv_spec)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (add_mod_left mod_add_mod zero_mod)
open E213.Meta.Nat.NatRing213 (nat_add_mul)
open E213.Meta.Algebra213.Ring213 (zero_mul)

/-- ★★★★ **The shifted per-term identity** — for a unit `j` (`0<j<p`, `gcd(j,p)=1`) and `0<k<p`,
    `χ_ω((j+k)%p)·conj χ_ω(j) = χ_ω((1+(k·(aInv j p % p))%p)%p)`.  Handles the wrap `(j+k)%p=0`
    (both sides `χ_ω(0)=0`).  ∅-axiom. -/
theorem chiOmega_shift_term {d : ZOmega} {p m x k j : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hk0 : 0 < k) (hkp : k < p) (hj1 : 0 < j) (hjp : j < p) (hjc : gcd213 j p = 1) :
    chiOmega p m x ((j + k) % p) * conj (chiOmega p m x j)
      = chiOmega p m x ((1 + (k * (aInv j p % p)) % p) % p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  -- (j·j⁻¹) % p = 1
  have hjw1 : (j * aInv j p) % p = 1 := by
    rw [aInv_spec hppos hjc, Nat.mod_eq_of_lt hp]
  -- the target index normalises to (1 + k·j⁻¹) % p
  have hidx : (1 + (k * (aInv j p % p)) % p) % p = (1 + k * aInv j p) % p := by
    rw [← mul_mod_right_pure k (aInv j p) p, Nat.add_comm 1 ((k * aInv j p) % p),
        mod_add_mod hppos (k * aInv j p) 1, Nat.add_comm (k * aInv j p) 1]
  -- (j·j⁻¹ + k·j⁻¹) % p = (1 + k·j⁻¹) % p   [using (j·j⁻¹)%p = 1]
  have hsum : (j * aInv j p + k * aInv j p) % p = (1 + k * aInv j p) % p := by
    rw [add_mod_left hppos (j * aInv j p) (k * aInv j p), hjw1]
  -- (j·j⁻¹ + k·j⁻¹) % p = (((j+k)%p)·j⁻¹) % p   [distribute, reduce]
  have hfac : (j * aInv j p + k * aInv j p) % p = ((j + k) % p * aInv j p) % p := by
    rw [← nat_add_mul j k (aInv j p), mul_mod_left_pure (j + k) (aInv j p) p]
  rw [hidx]
  rcases Nat.eq_zero_or_pos ((j + k) % p) with hz | hpos
  · -- wrap: both sides are χ_ω(0) = 0
    have hlhs : chiOmega p m x ((j + k) % p) = 0 := by
      rw [hz]; exact chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩
    have hzero : (1 + k * aInv j p) % p = 0 := by
      rw [← hsum, hfac, hz, Nat.zero_mul]; exact zero_mod p
    rw [hlhs, zero_mul, hzero, chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩]
  · -- unit numerator: chiOmega_div
    rw [chiOmega_div hp hp3 hpr h3m hdn hω hx hpos (Nat.mod_lt _ hppos) hj1 hjp hjc,
        ← hfac, hsum]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinShiftTerm
