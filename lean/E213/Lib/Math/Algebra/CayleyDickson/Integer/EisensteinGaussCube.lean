import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussNormSq
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSqZero
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm

/-!
# The Gauss-sum cube `g(χ)³ = J·(g⋆ḡ)` in the group ring (∅-axiom)

★★★★★ `gauss_cube` : in the free group ring `R[C_p]`, the cube of the cubic Gauss sum is the Jacobi
sum times the norm element:

  `(g ⋆ (g ⋆ g))(k) = J · Yfun p k`   for `k < p`,

where `Yfun p = p·e_0 − N` (`gauss_conj_norm`, the `g⋆ḡ` norm).  This is the group-ring form of the
classical `g(χ)³ = p·J`: in the cyclotomic quotient `ℤ[ζ_p]` the all-ones element `N = Σ_k e_k` maps
to `0` (`Σζ^k = 0`), so `J·(p·e_0 − N) ↦ p·J`.

## The chain

  `g⋆(g⋆g)`  =[`conv_assoc`]  `(g⋆g)⋆g`
             =[`gauss_sq_full` ⟶ `g⋆g = J·ḡ` coefficientwise]  `(J·ḡ)⋆g`
             =[`conv_scalar_left`]  `J·(ḡ⋆g)`
             =[`conv_comm`]  `J·(g⋆ḡ)`
             =[`gauss_conj_eq_Yfun`]  `J·Yfun`.

The key coefficient identity `(g⋆g)(j) = J·gaussConj(j)` (`gauss_sq_eq_J_gaussConj`) holds because
`g(χ²) = ḡ`: the square `χ_ω(j)²` of the cubic character equals the conjugate-Gauss-sum coefficient
`conj χ_ω((p−j)%p)` — using `χ_ω((p−j)%p) = χ_ω(j)` (`chiOmega_reflect`, since `p−1` is a cube and
`χ_ω(p−1)=1`) and `conj χ_ω = χ_ω²` (`conj_chiOmega_eq_sq`).  ∅-axiom throughout.

Feeds the Frobenius congruence step (B2) toward the cubic reciprocity law.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussCube

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
  (conv conv_congr conv_scalar_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc (conv_assoc)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm (conv_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSqZero (gauss_sq_full)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussNormSq (gauss_conj_eq_Yfun)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv (Yfun)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq (conj_chiOmega_eq_sq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm (conj_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex (not_dvd_of_pos_lt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (one_mul_zomega)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar cubicChar_one_iff_cube)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (negone_sq_mod_p)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge (neg_mul_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Meta.Nat.AddMod213 (mod_self)
open E213.Meta.Algebra213.Ring213 (zero_mul)

/-- **`χ_ω((p−i)%p) = χ_ω(i)`** for a unit `i` (`0 < i < p`).  Since `p−1` is a cube,
    `χ_ω(p−1)=1`, and `(p−i) ≡ (p−1)·i (mod p)`, so `χ_ω((p−i)%p) = χ_ω(p−1)·χ_ω(i) = χ_ω(i)`.
    The reflection underlying `g(χ²) = ḡ`.  ∅-axiom. -/
private theorem chiOmega_reflect {d : ZOmega} {p m x i : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hipos : 0 < i) (hilt : i < p) :
    chiOmega p m x ((p - i) % p) = chiOmega p m x i := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hpm1lt : p - 1 < p := Nat.sub_lt hppos (by decide)
  have hpm1pos : 1 ≤ p - 1 := Nat.le_pred_of_lt hp
  have hcube : (p - 1) ^ 3 % p = p - 1 := by
    have h2 : (p - 1) ^ 2 % p = 1 % p := by rw [Nat.pow_two]; exact negone_sq_mod_p p hp
    rw [show (p - 1) ^ 3 = (p - 1) ^ 2 * (p - 1) from rfl,
        mul_mod_left_pure ((p - 1) ^ 2) (p - 1) p, h2, Nat.mod_eq_of_lt hp, Nat.one_mul,
        Nat.mod_eq_of_lt hpm1lt]
  have hchi_pm1 : chiOmega p m x (p - 1) = ofInt 1 := by
    have hne : ¬ (p - 1) % p = 0 := by
      rw [Nat.mod_eq_of_lt hpm1lt]; exact Nat.ne_of_gt hpm1pos
    have hc1 : cubicChar p m (p - 1) = 1 :=
      (cubicChar_one_iff_cube p m (p - 1) hp hpr h3m hm1 hpm1pos hpm1lt).mpr
        ⟨p - 1, hpm1pos, hpm1lt, hcube⟩
    show (if (p - 1) % p = 0 then (0 : ZOmega) else
          if cubicChar p m (p - 1) = 1 then ofInt 1 else _) = ofInt 1
    rw [if_neg hne, if_pos hc1]
  have hnpi : ¬ p ∣ i := not_dvd_of_pos_lt hipos hilt
  have hidx : (p - i) % p = ((p - 1) * i) % p := by
    have hnm := neg_mul_mod i p 1 hp hpr hnpi (by decide) hp
    rw [Nat.mul_one, Nat.mod_eq_of_lt hilt] at hnm
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hppos hipos), Nat.mul_comm (p - 1) i, hnm]
  rw [hidx, ← chiOmega_mul hp hp3 hpr h3m hdn hω hx hpm1pos hpm1lt hipos hilt, hchi_pm1,
      one_mul_zomega]

/-- **`(g⋆g)(j) = J·ḡ(j)`** — the Gauss square is the Jacobi sum times the conjugate Gauss sum
    (`g(χ)² = J·g(χ̄)`), as a coefficient equation for `j < p`.  From `gauss_sq_full`
    (`(g⋆g)(j) = J·χ_ω(j)²`) plus `χ_ω(j)² = gaussConj(j)` (`chiOmega_reflect` + `conj_chiOmega_eq_sq`;
    both sides `0` at `j=0`).  ∅-axiom. -/
private theorem gauss_sq_eq_J_gaussConj {d : ZOmega} {p m x j : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hj : j < p) :
    conv p (gauss p m x) (gauss p m x) j = jacobiSum p m x * gaussConj p m x j := by
  rw [gauss_sq_full hp hp3 hpr h3m hm1 hdn hω hx hj]
  have hco : chiOmega p m x j * chiOmega p m x j = gaussConj p m x j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      show chiOmega p m x 0 * chiOmega p m x 0 = conj (chiOmega p m x ((p - 0) % p))
      rw [chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, Nat.sub_zero, mod_self,
          chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, conj_zero, zero_mul]
    · show chiOmega p m x j * chiOmega p m x j = conj (chiOmega p m x ((p - j) % p))
      rw [chiOmega_reflect hp hp3 hpr h3m hm1 hdn hω hx hpos hj, conj_chiOmega_eq_sq]
  rw [hco]

/-- ★★★★★ **The Gauss-sum cube** — `(g ⋆ (g ⋆ g))(k) = J·Yfun p k` for `k < p`, the group-ring form
    of `g(χ)³ = p·J` (`Yfun = p·e_0 − N`; in `ℤ[ζ_p]`, `N ↦ 0` recovers `p·J`).  Chain: `conv_assoc`
    to `(g⋆g)⋆g`, `gauss_sq_eq_J_gaussConj` (`g⋆g = J·ḡ`) under `conv_congr`, `conv_scalar_left` to
    pull `J` out, `conv_comm` to `g⋆ḡ`, then `gauss_conj_eq_Yfun`.  ∅-axiom. -/
theorem gauss_cube {d : ZOmega} {p m x k : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hk : k < p) :
    conv p (gauss p m x) (fun j => conv p (gauss p m x) (gauss p m x) j) k
      = jacobiSum p m x * Yfun p k := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  rw [← conv_assoc p (gauss p m x) (gauss p m x) (gauss p m x) hk,
      conv_congr p k hp0
        (fun i hi => gauss_sq_eq_J_gaussConj hp hp3 hpr h3m hm1 hdn hω hx hi)
        (fun _ _ => rfl),
      conv_scalar_left p (jacobiSum p m x) (gaussConj p m x) (gauss p m x) k,
      conv_comm p (gaussConj p m x) (gauss p m x) hk,
      gauss_conj_eq_Yfun hp hp3 hpr h3m hm1 hdn hω hx hk]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussCube
