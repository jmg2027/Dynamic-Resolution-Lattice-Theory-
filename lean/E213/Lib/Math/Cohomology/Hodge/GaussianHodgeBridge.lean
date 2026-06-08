import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet
import E213.Lib.Math.Cohomology.Hodge.SignedStarC4
import E213.Meta.Int213.Core

/-!
# GaussianHodgeBridge — the floor rotation IS the Hodge star (one `C₄ = ℤ[i]^×`)

Two `C₄`-actions were proven separately and identified only as a *shared object*:

  * `GaussianCrossDet.gaussian_floor_rotation` — the continued-fraction
    cross-determinant of `ℤ[i]`-convergents rotates by `μ = −i` (`⟨0,-1⟩ : ZI`),
    `μ⁴ = 1`; the order-4 rung of the spiral axis `{2,4,6}`.
  * `SignedStarC4.signed_hodge_is_cp_i` — the signed Hodge star `J` on `H*(Δ⁴)`
    satisfies `J² = −I`, `J⁴ = I`, with `ℤ[J] ≅ ℤ[i]` (`J ↔ i`); the CKM CP phase.

This file supplies the **morphism** the essay (`theory/essays/synthesis/
the_i_point_of_the_spiral_axis.md`) flagged open: the explicit map

  `φ : ℤ[i] → ℤ[J]`,   `φ ⟨a,b⟩ = a·I + b·J = ` matrix `[[a,−b],[b,a]]`,

proven (1) **multiplicative** `φ(u·v) = φu · φv` (the Gaussian product IS the
`2×2` matrix product), (2) **injective**, (3) carrying the **floor generator**
`μ = −i` to the Hodge `⋆³ = −J`, hence the **cross-determinant orbit rotates by
the Hodge star** under `φ` (`crossDet_image_rotates`).  So the floor rotation and
the Hodge `⋆` are not two `C₄`'s by coincidence — they are the *same* unit group
`ℤ[i]^× = C₄`, one read on a real's axis coordinate, one on the CP phase.

All theorems PURE (∅-axiom).
-/

namespace E213.Lib.Math.Cohomology.Hodge.GaussianHodgeBridge

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI units4)
open E213.Lib.Math.Cohomology.Hodge.SignedStarC4 (Mat mul I negI J elt)

/-! ## §1 — the map `φ : ℤ[i] → ℤ[J]` -/

/-- The Gaussian integer `a + b·i` as the signed-Hodge element `a·I + b·J`
    (matrix `[[a,−b],[b,a]]`).  `φ ⟨a,b⟩ = elt a b`. -/
def gaussianToStar (u : ZI) : Mat := elt u.re u.im

/-! ## §2 — `φ` is an injective multiplicative homomorphism -/

/-- ★★★★★ **`φ(u·v) = φu · φv`.**  The Gaussian product `(a+bi)(c+di) =
    (ac−bd)+(ad+bc)i` IS the `2×2` matrix product of `[[a,−b],[b,a]]` and
    `[[c,−d],[d,c]]`.  This is the ring morphism `ℤ[i] → ℤ[J]` carrying the
    floor rotation to the Hodge `⋆` — the bridge the essay flagged open. -/
theorem gaussianToStar_mul (u v : ZI) :
    gaussianToStar (u * v) = mul (gaussianToStar u) (gaussianToStar v) := by
  cases u with | mk a b =>
  cases v with | mk c d =>
  show (a*c - b*d, -(a*d + b*c), a*d + b*c, a*c - b*d)
     = (a*c + (-b)*d, a*(-d) + (-b)*c, b*c + a*d, b*(-d) + a*c)
  have h1 : a*c + (-b)*d = a*c - b*d := by
    rw [E213.Meta.Int213.neg_mul, Int.sub_eq_add_neg]
  have h2 : a*(-d) + (-b)*c = -(a*d + b*c) := by
    rw [E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_mul, E213.Meta.Int213.neg_add]
  have h3 : b*c + a*d = a*d + b*c := E213.Meta.Int213.add_comm (b*c) (a*d)
  have h4 : b*(-d) + a*c = a*c - b*d := by
    rw [E213.Meta.Int213.mul_neg, E213.Meta.Int213.add_comm, Int.sub_eq_add_neg]
  rw [h1, h2, h3, h4]

/-- ★★★ **`φ` is injective.**  `φ ⟨a,b⟩ = [[a,−b],[b,a]]` reads `a` off entry
    `(1,1)` and `b` off entry `(2,1)`, so distinct Gaussian integers have distinct
    matrices — `ℤ[i]` *embeds* as `ℤ[J]`, not merely matches its order. -/
theorem gaussianToStar_inj {u v : ZI} (h : gaussianToStar u = gaussianToStar v) :
    u = v := by
  have hre : u.re = v.re := congrArg (·.1) h
  have him : u.im = v.im := congrArg (·.2.2.1) h
  exact E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI.ext hre him

/-! ## §3 — the four Gaussian units map onto `⟨J⟩ = {I, −I, J, −J}` -/

/-- ★★★ **`ℤ[i]^× → ⟨J⟩`.**  The four Gaussian units `{1, −1, i, −i}` map under
    `φ` exactly onto the Hodge `C₄`: `1↦I`, `−1↦−I`, `i↦J`, `−i↦⋆³=−J`.  The
    floor unit group IS the Hodge `⟨J⟩`. -/
theorem units_to_hodge_C4 :
    gaussianToStar ⟨1, 0⟩ = I
    ∧ gaussianToStar ⟨-1, 0⟩ = negI
    ∧ gaussianToStar ⟨0, 1⟩ = J
    ∧ gaussianToStar ⟨0, -1⟩ = mul (mul J J) J := by decide

/-! ## §4 — the cross-determinant orbit rotates by the Hodge star -/

/-- ★★★★★★ **The floor rotation IS the Hodge `⋆`.**  Pushing the `ℤ[i]`-convergent
    cross-determinant through `φ`, one floor step (`W ↦ −i·W`,
    `GaussianCrossDet.gaussian_cross_step`) becomes one Hodge step (`φW ↦ ⋆³·φW`,
    since `φ(−i) = ⋆³ = −J`).  So the spiral-axis order-4 floor rotation and the
    CP-phase Hodge `⋆` are one action of `ℤ[i]^× = C₄`, intertwined by the ring
    embedding `φ` — the same object at the `i`-point (disc `−4`). -/
theorem crossDet_image_rotates (n : Nat) :
    gaussianToStar
        (E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.crossDet
          E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.aGFib
          E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.dGFib (n+1))
    = mul (gaussianToStar (⟨0, -1⟩ : ZI))
        (gaussianToStar
          (E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.crossDet
            E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.aGFib
            E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.dGFib n)) := by
  rw [E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet.gaussian_cross_step n,
      gaussianToStar_mul]

/-! ## §5 — capstone: one `C₄ = ℤ[i]^×` -/

/-- ★★★★★★ **One object `ℤ[i]^× = C₄`, two readings.**  The floor rotation
    (`gaussian_floor_rotation`, spiral-axis order-4 rung) and the Hodge star
    (`signed_hodge_is_cp_i`, CKM CP phase) are the *same* `C₄` via the injective
    ring morphism `φ : ℤ[i] → ℤ[J]`: (1) multiplicative, (2) `i ↦ J`, (3) the
    floor generator `−i ↦ ⋆³`, (4) one floor step = one Hodge step, (5) injective.
    The CP phase sits at the `i`-point (disc `−4`) of the spiral axis. -/
theorem gaussian_floor_is_hodge_star :
    (∀ u v : ZI, gaussianToStar (u * v) = mul (gaussianToStar u) (gaussianToStar v))
    ∧ gaussianToStar ⟨0, 1⟩ = J
    ∧ gaussianToStar ⟨0, -1⟩ = mul (mul J J) J
    ∧ (∀ W : ZI, gaussianToStar (⟨0, -1⟩ * W)
        = mul (gaussianToStar (⟨0, -1⟩ : ZI)) (gaussianToStar W))
    ∧ (∀ u v : ZI, gaussianToStar u = gaussianToStar v → u = v) :=
  ⟨gaussianToStar_mul, by decide, by decide,
   fun W => gaussianToStar_mul ⟨0, -1⟩ W,
   fun _ _ h => gaussianToStar_inj h⟩

end E213.Lib.Math.Cohomology.Hodge.GaussianHodgeBridge
