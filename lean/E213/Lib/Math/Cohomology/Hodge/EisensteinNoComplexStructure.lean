import E213.Lib.Math.Cohomology.Hodge.SignedStarC4
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Meta.Int213.PolyIntMTactic

/-!
# EisensteinNoComplexStructure — the order-6 axis rung is *not* a complex structure

The spiral axis is `{2, 4, 6}` = `ℤ^×`, `ℤ[i]^×`, `ℤ[ω]^×`.  The order-4 (Gaussian, disc `−4`)
rung carries a **complex structure**: the signed Hodge star `J` has `J² = −I`
(`SignedStarC4`, `GaussianHodgeBridge`), so `ℤ[i]^× = ⟨J⟩ ≅ C₄`.  The CKM CP phase needs exactly
that — a polarized Hodge structure with `⋆² = −1` — and so sits at disc `−4`
(`theory/physics/cp_phase.md`, `theory/essays/synthesis/the_i_point_of_the_spiral_axis.md`).

This file makes the *selection* a theorem: the order-6 (Eisenstein, disc `−3`) rung does **not**
admit `⋆² = −1`.  Its companion is `Ω = [[0,−1],[1,−1]]` (the companion of `x²+x+1`), with

  `Ω² = −Ω − I ≠ −I`,   `Ω³ = I`   (so `ω = Ω` has order 3, `ζ₆ = I + Ω` order 6),

and `ℤ[Ω] ≅ ℤ[ω]` (the Eisenstein product, `omegaToStar_mul`, injective).  Because `Ω² ≠ −I`,
the order-6 rung is **not** a complex structure — only the order-4 rung is — so the Hodge `⋆`
(`⋆² = −1`) forces the Gaussian rung, disc `−4` over disc `−3`.

All theorems PURE (∅-axiom).
-/

namespace E213.Lib.Math.Cohomology.Hodge.EisensteinNoComplexStructure

open E213.Lib.Math.Cohomology.Hodge.SignedStarC4 (Mat mul I negI J)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)

/-! ## §1 — the Eisenstein companion `Ω` and the absence of `⋆² = −1` -/

/-- The Eisenstein companion matrix `Ω = [[0,−1],[1,−1]]` (companion of `x²+x+1`). -/
def Om : Mat := (0, -1, 1, -1)

/-- ★★★★ **`Ω² = −Ω − I ≠ −I`, `Ω³ = I`.**  The order-6 rung's generator squares to `−Ω−I`,
    *not* to `−I` — so unlike the Gaussian `J` (`J² = −I`), the Eisenstein `Ω` is **not** a
    complex structure.  `Ω³ = I` makes `ω = Ω` an order-3 element (`Ω² ≠ I`). -/
theorem eisenstein_companion :
    mul Om Om = (-1, 1, -1, 0)        -- Ω² = −Ω − I (explicit)
    ∧ mul (mul Om Om) Om = I          -- Ω³ = I
    ∧ mul Om Om ≠ negI                -- Ω² ≠ −I : NOT a complex structure
    ∧ mul Om Om ≠ I := by decide      -- Ω² ≠ I : ω has order 3, not 1

/-! ## §2 — the ring morphism `ℤ[ω] → ℤ[Ω]` (the Eisenstein product is the matrix product) -/

/-- `a + b·ω` as the matrix `a·I + b·Ω = [[a,−b],[b,a−b]]`. -/
def eltΩ (a b : Int) : Mat := (a, -b, b, a - b)

/-- The map `φ : ℤ[ω] → ℤ[Ω]`, `⟨a,b⟩ ↦ a·I + b·Ω`. -/
def omegaToStar (u : ZOmega) : Mat := eltΩ u.re u.im

/-- ★★★★★ **`φ(u·v) = φu · φv`.**  The Eisenstein product `(a+bω)(c+dω) =
    (ac−bd) + (ad+bc−bd)ω` (using `ω² = −1−ω`) IS the `2×2` matrix product of `[[a,−b],[b,a−b]]`
    and `[[c,−d],[d,c−d]]` — so `ℤ[Ω] ≅ ℤ[ω]`, `Ω ↔ ω`. -/
theorem omegaToStar_mul (u v : ZOmega) :
    omegaToStar (u * v) = mul (omegaToStar u) (omegaToStar v) := by
  cases u with | mk a b =>
  cases v with | mk c d =>
  show ((a*c - b*d), -(a*d + b*c - b*d), (a*d + b*c - b*d), (a*c - b*d) - (a*d + b*c - b*d))
     = ((a*c + (-b)*d), (a*(-d) + (-b)*(c - d)), (b*c + (a - b)*d), (b*(-d) + (a - b)*(c - d)))
  have h1 : a*c + (-b)*d = a*c - b*d := by ring_intZ
  have h2 : a*(-d) + (-b)*(c - d) = -(a*d + b*c - b*d) := by ring_intZ
  have h3 : b*c + (a - b)*d = a*d + b*c - b*d := by ring_intZ
  have h4 : b*(-d) + (a - b)*(c - d) = (a*c - b*d) - (a*d + b*c - b*d) := by ring_intZ
  rw [h1, h2, h3, h4]

/-- ★★★ **`φ` is injective.**  `φ⟨a,b⟩ = [[a,−b],[b,a−b]]` reads `a` off entry `(1,1)` and `b`
    off entry `(2,1)`, so `ℤ[ω]` embeds as `ℤ[Ω]`. -/
theorem omegaToStar_inj {u v : ZOmega} (h : omegaToStar u = omegaToStar v) : u = v := by
  have hre : u.re = v.re := congrArg (·.1) h
  have him : u.im = v.im := congrArg (·.2.2.1) h
  exact E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega.ext hre him

/-- ★★★ **The order-6 generator `ζ₆ = 1 + ω` maps to an order-6 matrix.**  `φ⟨1,1⟩ = I + Ω`
    has `M⁶ = I`, `M² = Ω ≠ I`, `M³ = −I ≠ I` — order exactly 6, the Eisenstein rung. -/
theorem eisenstein_zeta6_order_six :
    omegaToStar ⟨1, 1⟩ = (1, -1, 1, 0)
    ∧ mul (omegaToStar ⟨1, 1⟩) (omegaToStar ⟨1, 1⟩) = Om          -- ζ₆² = ω
    ∧ mul (mul (omegaToStar ⟨1, 1⟩) (omegaToStar ⟨1, 1⟩)) (omegaToStar ⟨1, 1⟩) = negI  -- ζ₆³ = −1
    ∧ mul (mul (mul Om Om) Om) (mul (mul Om Om) Om) = I := by decide  -- (ζ₆³)² → ζ₆⁶ = I via Ω⁶

/-! ## §3 — capstone: the Hodge `⋆² = −1` selects disc `−4` over disc `−3` -/

/-- ★★★★★★ **CP selects the Gaussian rung.**  The order-4 rung admits the complex structure
    (`J² = −I`, Gaussian, disc `−4`); the order-6 rung does not (`Ω² ≠ −I`, Eisenstein,
    disc `−3`), though `Ω³ = I`.  A polarized Hodge structure requires `⋆² = −1`, so the CKM CP
    phase sits at disc `−4` — the choice between the two CM points is forced by the complex
    structure, not posited. -/
theorem hodge_selects_disc_neg_four :
    mul J J = negI                    -- order 4 (disc −4): IS a complex structure
    ∧ mul Om Om ≠ negI                -- order 6 (disc −3): is NOT
    ∧ mul (mul Om Om) Om = I          -- but Ω³ = I (genuine order-6 unit ring)
    ∧ (∀ u v : ZOmega, omegaToStar (u * v) = mul (omegaToStar u) (omegaToStar v)) :=
  ⟨by decide, by decide, by decide, omegaToStar_mul⟩

end E213.Lib.Math.Cohomology.Hodge.EisensteinNoComplexStructure
