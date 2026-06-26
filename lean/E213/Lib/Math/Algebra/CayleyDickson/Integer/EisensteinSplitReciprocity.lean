import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitCube
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv

/-!
# The split-prime reciprocity congruence — `J^{s+1}·p^{s+1} ≡ χ̄(pr) (mod ofInt pr)` (∅-axiom)

★★★★★ `split_reciprocity_congr` : for a split second prime `pr = 3(s+1)+1 ≡ 1 (mod 3)` (a unit mod `p`),

  `J^{s+1} · p^{s+1} ≡ χ̄(pr)   (mod ofInt pr)`        (`J = jacobiSum`).

Equates the two evaluations of `g(χ)^{⋆pr}(1)`:
- **cube side** `gauss_convPow_split` (`= J^{s+1}·p^{s+1}·g(1) = J^{s+1}·p^{s+1}`, since `g(1) = χ(1) = 1`);
- **Frobenius side** `gauss_pow_modEq_char_factored` (`≡ χ̄(pr)·χ(1) = χ̄(pr) (mod ofInt pr)`).

The split analog of `cubic_reciprocity_congr` (`J^{s+1}·p^s ≡ χ(q)` for inert `q`); note `g(1) = 1` plays
the unit-cancellation role that `Yfun(1) = −1` played in the inert case, and the character is conjugated
(`χ̄(pr)`, vs the inert `χ(q)`).  This descends to `mod π'` via `π' ∣ ofInt pr` (`split_fermat`).
∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitReciprocity

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv (chiOmega_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow (convPow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitCube (gauss_convPow_split)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex (gauss_pow_modEq_char_factored)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd (mul_ofInt_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Tactic.NatHelper (gcd213)

/-- ★★★★★ **The split-prime reciprocity congruence** — `J^{s+1}·p^{s+1} ≡ χ̄(pr) (mod ofInt pr)` for a
    split prime `pr = 3(s+1)+1`, unit mod `p` (`p > 3`).  Cube side `=` Frobenius side at `k = 1`.
    ∅-axiom (PURE). -/
theorem split_reciprocity_congr {d : ZOmega} {p m x pr s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hpr3 : pr % 3 = 1) (hprr : ∀ e, e ∣ pr → e = 1 ∨ e = pr)
    (hcop : gcd213 pr p = 1) (hpr1 : 1 < pr) (hprlt : pr < p) (hs : pr = 3 * (s + 1) + 1) :
    ModEq (ofInt ((pr : Nat) : Int))
      (pow (jacobiSum p m x) (s + 1) * pow (ofInt ((p : Nat) : Int)) (s + 1))
      (conj (chiOmega p m x pr)) := by
  have h1lt : (1 : Nat) < p := hp
  have hprpos : 0 < pr := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hpr1)
  have hg1 : gauss p m x 1 = ofInt 1 := chiOmega_one h1lt
  have hc1 : chiOmega p m x 1 = ofInt 1 := chiOmega_one h1lt
  -- cube side at k = 1, simplified `g(1) = 1`
  have hcube := gauss_convPow_split (s := s) hp hp3 hpr h3m hm1 hdn hω hx (k := 1) h1lt
  rw [← hs, hg1, mul_ofInt_one] at hcube
  -- Frobenius side at k = 1, simplified `χ(1) = 1`
  have hfrob := gauss_pow_modEq_char_factored hp hp3 hpr h3m hdn hω hx hpr1 hpr3 hprr hcop
    hprpos hprlt (k := 1) (by decide) h1lt
  rw [hc1, mul_ofInt_one, hcube] at hfrob
  exact hfrob

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitReciprocity
