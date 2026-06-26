import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFourSwap
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne

/-!
# `(g·g)·(ḡ·ḡ) = p·Y` — the norm-square transported to the Gauss-square form (∅-axiom, A3 / route b)

Combining the reassociation `(g·ḡ)² = (g·g)·(ḡ·ḡ)` (`conv_four_swap`), the norm `g·ḡ = Y`
(`gauss_conj_norm`, i.e. `conv gauss gaussConj = Yfun` on `[0,p)`), and `Y⋆Y = p·Y` (`Yfun_conv`):

  `(g⋆g) ⋆ (conj g ⋆ conj g) (k) = ofInt(↑p) · Yfun p k`   (`gg_gbgb_eq`),  for `k < p`.

With the Gauss–Jacobi relation `g⋆g = J·g(χ²)` (and its conjugate), reading off the `e_1`-coefficient
(`Yfun 1 = −1 ≠ 0`) gives the Jacobi-sum norm law `N(J) = |J|² = p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussNormSq

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv conv_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne (gauss_conj_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv (Yfun Yfun_conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFourSwap (conv_four_swap)

/-- `conv gauss gaussConj k = Yfun p k` for `k < p` — the norm `g·ḡ = Y` as a coefficient equation
    (`gauss_conj_norm`, whose RHS is `Yfun p k` by definition).  ∅-axiom. -/
theorem gauss_conj_eq_Yfun {d : ZOmega} {p m x k : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hkp : k < p) :
    conv p (gauss p m x) (gaussConj p m x) k = Yfun p k := by
  unfold Yfun
  exact gauss_conj_norm hp hp3 hpr h3m hm1 hdn hω hx hkp

/-- ★★★★★ **The Gauss-square norm** — `(g⋆g)⋆(ḡ⋆ḡ)(k) = ofInt(↑p)·Yfun p k` for `k < p`.
    `conv_four_swap` + `gauss_conj_eq_Yfun` (via `conv_congr`) + `Yfun_conv`.  ∅-axiom. -/
theorem gg_gbgb_eq {d : ZOmega} {p m x k : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hk : k < p) :
    conv p (fun j => conv p (gauss p m x) (gauss p m x) j)
        (fun j => conv p (gaussConj p m x) (gaussConj p m x) j) k
      = ofInt ((p : Nat) : Int) * Yfun p k := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  rw [← conv_four_swap p (gauss p m x) (gaussConj p m x) hk,
      conv_congr p k hp0
        (fun i hi => gauss_conj_eq_Yfun hp hp3 hpr h3m hm1 hdn hω hx hi)
        (fun i hi => gauss_conj_eq_Yfun hp hp3 hpr h3m hm1 hdn hω hx hi)]
  exact Yfun_conv (Nat.le_of_lt hp) hk

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussNormSq
