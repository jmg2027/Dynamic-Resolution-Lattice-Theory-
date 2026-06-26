import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobi
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative

/-!
# The `n=0` Gauss-square coefficient — `(g⋆g)(0) = 0` (∅-axiom, Phase A3 / route b)

The diagonal coefficient of `g(χ)²`:

  `(g ⋆ g)(0) = Σ_i χ_ω(i)·χ_ω((p−i)%p) = Σ_{i∈tot} χ_ω(i)² = 0`   (`gauss_sq_zero`).

The `i=0` term drops (`χ_ω(0)=0`); for a unit `i`, `χ_ω((p−i)%p) = χ_ω(i)` because `p−i ≡ (p−1)·i`
and `χ_ω(p−1)=1` (`p−1 = (p−1)³ mod p` is a cube).  The remaining `Σ χ_ω(i)² = 0` is the
`χ²`-orthogonality (`chiOmega_sq_orth`).  This completes `g(χ)² = J·g(χ²)` at **all** coefficients
(`g(χ²)(0) = χ_ω(0)² = 0`), as needed for the four-factor reassembly giving `N(J)=p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSqZero

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobi (gauss_sq_unit)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq (chiOmega_sq_orth)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex (not_dvd_of_pos_lt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (one_mul_zomega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (sumRange_eq_listSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives
  (listSum_rangeList_split)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_pos totativeList_le totativeList_coprime totative_lt_n)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar cubicChar_one_iff_cube)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (negone_sq_mod_p)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge (neg_mul_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Meta.Algebra213.Ring213 (zero_mul zero_add)

/-- ★★★★★ **The `n=0` Gauss-square coefficient** — `(g⋆g)(0) = 0`.  `χ_ω((p−i)%p)=χ_ω(i)` (since
    `p−1` is a cube, `χ_ω(p−1)=1`), reducing to `χ²`-orthogonality.  ∅-axiom. -/
theorem gauss_sq_zero {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    conv p (gauss p m x) (gauss p m x) 0 = 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hpm1lt : p - 1 < p := Nat.sub_lt hppos (by decide)
  have hpm1pos : 1 ≤ p - 1 := Nat.le_pred_of_lt hp
  -- p−1 is a cube: (p−1)³ ≡ p−1
  have hcube : (p - 1) ^ 3 % p = p - 1 := by
    have h2 : (p - 1) ^ 2 % p = 1 % p := by rw [Nat.pow_two]; exact negone_sq_mod_p p hp
    rw [show (p - 1) ^ 3 = (p - 1) ^ 2 * (p - 1) from rfl,
        mul_mod_left_pure ((p - 1) ^ 2) (p - 1) p, h2, Nat.mod_eq_of_lt hp, Nat.one_mul,
        Nat.mod_eq_of_lt hpm1lt]
  -- χ_ω(p−1) = 1
  have hchi_pm1 : chiOmega p m x (p - 1) = ofInt 1 := by
    have hne : ¬ (p - 1) % p = 0 := by
      rw [Nat.mod_eq_of_lt hpm1lt]; exact Nat.ne_of_gt hpm1pos
    have hc1 : cubicChar p m (p - 1) = 1 :=
      (cubicChar_one_iff_cube p m (p - 1) hp hpr h3m hm1 hpm1pos hpm1lt).mpr
        ⟨p - 1, hpm1pos, hpm1lt, hcube⟩
    show (if (p - 1) % p = 0 then (0 : ZOmega) else
          if cubicChar p m (p - 1) = 1 then ofInt 1 else _) = ofInt 1
    rw [if_neg hne, if_pos hc1]
  -- assemble
  show sumRange (fun i => chiOmega p m x i * chiOmega p m x ((0 + p - i) % p)) p = 0
  rw [sumRange_eq_listSum, listSum_rangeList_split _ hp hpr,
      show chiOmega p m x 0 * chiOmega p m x ((0 + p - 0) % p) = 0 from by
        rw [chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, zero_mul], zero_add,
      listSum_congr (totativeList p) (fun i hi => by
        have hipos : 0 < i := totativeList_pos hi
        have hilt : i < p :=
          totative_lt_n hp (totativeList_coprime hi) (totativeList_pos hi) (totativeList_le hi)
        have hnpi : ¬ p ∣ i := not_dvd_of_pos_lt hipos hilt
        have hidx : (p - i) % p = ((p - 1) * i) % p := by
          have hnm := neg_mul_mod i p 1 hp hpr hnpi (by decide) hp
          rw [Nat.mul_one, Nat.mod_eq_of_lt hilt] at hnm
          rw [Nat.mod_eq_of_lt (Nat.sub_lt hppos hipos), Nat.mul_comm (p - 1) i, hnm]
        have hchineg : chiOmega p m x ((0 + p - i) % p) = chiOmega p m x i := by
          rw [Nat.zero_add, hidx,
              ← chiOmega_mul hp hp3 hpr h3m hdn hω hx hpm1pos hpm1lt hipos hilt, hchi_pm1,
              one_mul_zomega]
        rw [hchineg])]
  exact chiOmega_sq_orth hp hp3 hpr h3m hm1 hdn hω hx

/-- ★★★★★ **The Gauss–Jacobi relation at every coefficient** — `(g⋆g)(n) = jacobiSum·χ_ω(n)²` for all
    `n < p` (`g(χ)² = J·g(χ²)` in `R[C_p]`, since `g(χ²)(n) = χ_ω(n)²`).  Unit `n`: `gauss_sq_unit`;
    `n=0`: `gauss_sq_zero` (both sides `0`).  ∅-axiom. -/
theorem gauss_sq_full {d : ZOmega} {p m x n : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hn : n < p) :
    conv p (gauss p m x) (gauss p m x) n
      = jacobiSum p m x * (chiOmega p m x n * chiOmega p m x n) := by
  rcases Nat.eq_zero_or_pos n with hz | hpos
  · subst hz
    rw [gauss_sq_zero hp hp3 hpr h3m hm1 hdn hω hx,
        chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, zero_mul,
        E213.Meta.Algebra213.Ring213.mul_zero]
  · exact gauss_sq_unit hp hp3 hpr h3m hdn hω hx hpos hn

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSqZero
