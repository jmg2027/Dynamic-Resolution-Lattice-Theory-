import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitCube
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitFermat
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiPrime

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
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiPrime (jacobi_splits_p)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (pow_add pow_mul_distrib)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitFermat (modEq_descend)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)
open E213.Meta.Algebra213.Ring213 (mul_assoc)

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

/-- ★★★★★ **The split reciprocity congruence, all-Eisenstein form** — eliminating `p = J·J̄`
    (`jacobi_splits_p`):

      `J^{2(s+1)} · J̄^{s+1} ≡ χ̄(pr)   (mod ofInt pr)`        (`J = jacobiSum`).

    `pow_mul_distrib` splits `(J·J̄)^{s+1} = J^{s+1}·J̄^{s+1}`, `pow_add` merges `J^{s+1}·J^{s+1} =
    J^{2(s+1)}`.  Purely in the Eisenstein prime `J = π` and its conjugate — the symmetric form the
    `π ↔ π'` transfer consumes (split analog of `cubic_reciprocity_congr_eisenstein`).  ∅-axiom (PURE). -/
theorem split_reciprocity_congr_eisenstein {d : ZOmega} {p m x pr s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hpr3 : pr % 3 = 1) (hprr : ∀ e, e ∣ pr → e = 1 ∨ e = pr)
    (hcop : gcd213 pr p = 1) (hpr1 : 1 < pr) (hprlt : pr < p) (hs : pr = 3 * (s + 1) + 1) :
    ModEq (ofInt ((pr : Nat) : Int))
      (pow (jacobiSum p m x) (2 * (s + 1)) * pow (conj (jacobiSum p m x)) (s + 1))
      (conj (chiOmega p m x pr)) := by
  have hcong := split_reciprocity_congr hp hp3 hpr h3m hm1 hdn hω hx hpr3 hprr hcop hpr1 hprlt hs
  have heq : pow (jacobiSum p m x) (s + 1) * pow (ofInt ((p : Nat) : Int)) (s + 1)
      = pow (jacobiSum p m x) (2 * (s + 1)) * pow (conj (jacobiSum p m x)) (s + 1) := by
    rw [← jacobi_splits_p hp hp3 hpr h3m hm1 hdn hω hx,
        pow_mul_distrib (jacobiSum p m x) (conj (jacobiSum p m x)) (s + 1),
        ← mul_assoc, ← pow_add (jacobiSum p m x) (s + 1) (s + 1),
        show (s + 1) + (s + 1) = 2 * (s + 1) from by rw [Nat.two_mul]]
  rw [heq] at hcong
  exact hcong

/-- ★★★★★ **The split reciprocity congruence, modulo the second prime `π'`** —
    `J^{2(s+1)}·J̄^{s+1} ≡ χ̄(pr) (mod π')` for an Eisenstein prime `π'` of norm `pr`.  Descent of the
    all-Eisenstein form along `π' ∣ ofInt pr` (`π'·π̄' = ofInt ‖π'‖² = ofInt pr`, `mul_conj_self`) via
    `modEq_descend`.  The congruence now lives in `𝔽_{p'} = ℤ[ω]/(π')`, where the `𝔽_{p'}`-Fermat
    (`split_fermat`) collapses the `J̄` powers to the cubic residue symbol `(π/π')₃`.  ∅-axiom (PURE). -/
theorem split_reciprocity_congr_pi {d : ZOmega} {p m x pr s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hpr3 : pr % 3 = 1) (hprr : ∀ e, e ∣ pr → e = 1 ∨ e = pr)
    (hcop : gcd213 pr p = 1) (hpr1 : 1 < pr) (hprlt : pr < p) (hs : pr = 3 * (s + 1) + 1)
    {π' : ZOmega} (hπ'norm : π'.normSq = (pr : Int)) :
    ModEq π' (pow (jacobiSum p m x) (2 * (s + 1)) * pow (conj (jacobiSum p m x)) (s + 1))
      (conj (chiOmega p m x pr)) := by
  have hbase := split_reciprocity_congr_eisenstein hp hp3 hpr h3m hm1 hdn hω hx hpr3 hprr hcop
    hpr1 hprlt hs
  have hdvd : π' ∣ ofInt ((pr : Nat) : Int) := ⟨conj π', by rw [mul_conj_self π', hπ'norm]⟩
  exact modEq_descend hdvd hbase

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitReciprocity
