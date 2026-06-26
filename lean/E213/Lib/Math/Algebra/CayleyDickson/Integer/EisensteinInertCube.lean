import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertPrime
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue

/-!
# Cube roots of unity in `𝔽_{q²} = ℤ[ω]/(q)` are `1, ω, ω²` (∅-axiom)

★★★★★ `inert_cube_one_value` : for an inert rational prime `q ≡ 2 (mod 3)`, anything cubing to `1`
modulo `q` is congruent to one of the three cube roots of unity:

  `y³ ≡ 1 (mod q)   ⟹   y ≡ 1 ∨ y ≡ ω ∨ y ≡ ω²   (mod q)`.

`cubic_factor` turns `q ∣ (y³ − 1)` into `q ∣ (y−1)·((y−ω)·(y−ω²))`; `inert_residue_no_zero_divisors`
(`ℤ[ω]/(q)` is a domain, since `q` is prime in `ℤ[ω]`) applied twice splits the triple product.

This is the **existence** half of the cubic residue symbol `(π/q)₃`: once `J^{(q²−1)/3}` is known to cube
to `1` mod `q` (`frob_sq` + `J` a unit mod `q`), this lands it in `μ₃ = {1,ω,ω²}`, and `mu3_eq_of_modEq`
pins the value.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertCube

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega Omega2)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Meta.Algebra213.Ring213 (add_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertPrime
  (inert_residue_no_zero_divisors)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue (cubic_factor)

private theorem hz0 : (-(0 : ZOmega)) = 0 := by decide

/-- `ModEq d (a + -b) 0 ⟹ ModEq d a b` — both are `d ∣ (a + -b)` (the `-0` drops). -/
private theorem modEq_of_sub_zero {d a b : ZOmega} (h : ModEq d (a + -b) 0) : ModEq d a b := by
  have h2 : d ∣ ((a + -b) + -0) := h
  rw [hz0, add_zero] at h2; exact h2

/-- `d ∣ x ⟹ ModEq d x 0` — package a divisibility as a `ModEq · 0`. -/
private theorem modEq_zero_of_dvd {d x : ZOmega} (h : d ∣ x) : ModEq d x 0 := by
  show d ∣ (x + -0); rw [hz0, add_zero]; exact h

/-- ★★★★★ **A cube root of unity in `ℤ[ω]/(q)` is `1`, `ω`, or `ω²`** for an inert prime `q ≡ 2 (mod 3)`.
    `cubic_factor` + `inert_residue_no_zero_divisors` (twice).  ∅-axiom (PURE). -/
theorem inert_cube_one_value {q : Nat} (hq3 : q % 3 = 2)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hq1 : 1 < q) {y : ZOmega}
    (hcube : ModEq (ofInt (q : Int)) (y * y * y) (ofInt 1)) :
    ModEq (ofInt (q : Int)) y (ofInt 1) ∨ ModEq (ofInt (q : Int)) y Omega
      ∨ ModEq (ofInt (q : Int)) y Omega2 := by
  have hdvd : ofInt (q : Int) ∣ ((y + -(ofInt 1)) * ((y + -Omega) * (y + -Omega2))) := by
    have h1 : ofInt (q : Int) ∣ (y * y * y + -(ofInt 1)) := hcube
    rwa [cubic_factor y] at h1
  rcases inert_residue_no_zero_divisors hq3 hqr hq1 (modEq_zero_of_dvd hdvd) with hA | hBC
  · exact Or.inl (modEq_of_sub_zero hA)
  · rcases inert_residue_no_zero_divisors hq3 hqr hq1 hBC with hO | hO2
    · exact Or.inr (Or.inl (modEq_of_sub_zero hO))
    · exact Or.inr (Or.inr (modEq_of_sub_zero hO2))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertCube
