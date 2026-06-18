import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexT2
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexT2Squared
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexP2
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexP1Squared
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemann
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemannT2
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemannT2Squared
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.BalancedSignature
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexGradeStructure
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.KahlerGradeStructure
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.SurfaceComparisonTheorem
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.T2nPattern
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.T2nInductive
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.TensorSignature
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.GenusGSurface
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.ProductSurfaceSignature
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.TripleProductSurface
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.TripleProductSurfaceParametric

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.HodgeConjecture.Pairing`.

  Cup-pairing signatures (Hodge index + Hodge–Riemann) on real
  CW surfaces and their products.  These are the genuine
  intersection-form / signature results; coefficient sign and
  positivity are supplied at the signed-ℤ level (`HodgeRiemann`).

  ## Files

    * `HodgeIndexT2`           — ★ T² (genus 1): signature (1, 1) on H¹
    * `HodgeIndexT2Squared`    — ★ T²×T² (4-fold): signature (3, 3)
                                  on H², three hyperbolic blocks
    * `HodgeIndexP2`           — ★ ℙ²: signature (1, 0) on H²
    * `HodgeIndexP1Squared`    — ★ ℙ¹×ℙ¹: signature (1, 1) on H²
                                  (distinct Hodge structure from T²)
    * `HodgeRiemann`           — signed-ℤ Hodge–Riemann positivity:
                                  polarization (Q, J), `h = Q·J = I ≻ 0`
    * `HodgeRiemannT2`         — ★ Kähler class with `cup(ω, ω) > 0` on T²
    * `HodgeRiemannT2Squared`  — ★★★ HR ℚ-positivity on T²×T² (1,1)
                                  primitive part: cup on `P^{1,1}` is
                                  diag(−2,−2,−2), negative-definite
    * `T2nPattern`             — ★★ `signature(H^n; T²ⁿ) =
                                  (½·C(2n,n), ½·C(2n,n))`, n ≤ 5
    * `T2nInductive`           — ★★★ full inductive form, all n ≥ 1
    * `TensorSignature`        — ★★★ Künneth signature pair rule
                                  `(p·p' + q·q', p·q' + q·p')`
    * `GenusGSurface`          — ★★★ `signature(Σ_g) = (g, g)`, all g ≥ 0,
                                  connected-sum additivity
    * `SurfaceComparisonTheorem` — ★★ comparison across 4 Kähler 2-folds
                                  (T², ℙ², ℙ¹×ℙ¹, T²×T²)
    * `ProductSurfaceSignature`,
      `TripleProductSurface*`  — Σ_g × Σ_h (and triple) product signatures
-/
