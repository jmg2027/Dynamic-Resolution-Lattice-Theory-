import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndex
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexT2
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexT2Squared
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexP2
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexP1Squared
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemann
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemannT2
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemannT2Squared
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.BalancedSignature
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HirzebruchMultiplicative
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndexGradeStructure
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.KahlerGradeStructure
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.SurfaceComparisonTheorem
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.T2nPattern
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.T2nInductive
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.TensorSignature
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.GenusGSurface
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.SignatureMetaTheorem
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.ProductSurfaceSignature
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.TripleProductSurface
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.TripleProductSurfaceParametric

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.HodgeConjecture.Pairing`.

  Pairings on H* — Hodge index + Hodge–Riemann.

  ## Files

    * `HodgeIndex`             — base capstone on K_{3,2}^{(c=2)}
                                  (graph; cup-pairing vacuously zero)
    * `HodgeIndexT2`           — ★ Non-vacuous lift to T² (genus 1):
                                  signature (1, 1) on H¹
    * `HodgeIndexT2Squared`    — ★ Hodge Index on T²×T² (4-fold):
                                  signature (3, 3) on H², three
                                  hyperbolic blocks
    * `HodgeIndexP2`           — ★ Hodge Index on ℙ² (h^{2,0}=0,
                                  h^{1,1}=1): signature (1, 0) on H²
    * `HodgeIndexP1Squared`    — ★ Hodge Index on ℙ¹×ℙ¹
                                  (h^{2,0}=0, h^{1,1}=2):
                                  signature (1, 1) — same as T²
                                  but distinct Hodge structure
    * `HodgeRiemann`           — base capstone on K_{3,2}^{(c=2)}
                                  (positivity vacuous in ℤ/2)
    * `HodgeRiemannT2`         — ★ Non-vacuous lift: Kähler class
                                  with `cup(ω, ω) > 0` on T²
    * `HodgeRiemannT2Squared`  — ★★★ **HR ℚ-positivity refinement
                                  on T²×T² (1,1) primitive part**:
                                  closes  by exhibiting 3
                                  primitive (1,1) classes η₁, η₂, η₃
                                  with `cup(η_i, η_i) = −2 < 0`
                                  and mutual orthogonality.
                                  Cup-pairing on `P^{1,1}` is
                                  diag(−2,−2,−2) — negative-definite
                                  per classical HR.  STRICT ∅-AXIOM.
    * `T2nPattern`             — ★★ **Pattern theorem**:
                                  `signature(H^n; T²ⁿ) =
                                   (½·C(2n,n), ½·C(2n,n))`,
                                  bundling all n=1, n=2 witnesses
                                  + numerical sequence for n≤5
    * `T2nInductive`           — ★★★ **Pattern theorem (full
                                  inductive form)**: parametric
                                  `T2n_blocks_inductive n hn`
                                  closes the open follow-up from
                                  `BalancedSignature.lean` for
                                  every `n ≥ 1`, via binom symmetry
                                  `central_binom_is_double`.
                                  STRICT ∅-AXIOM.
    * `TensorSignature`        — ★★★ **Tensor / Künneth signature
                                  theorem on (pos, neg) pair**:
                                  closes  follow-up by
                                  refining Hirzebruch multiplicativity
                                  from σ-only to the full pair-level
                                  Künneth rule `(p·p' + q·q',
                                  p·q' + q·p')`.  STRICT ∅-AXIOM.
    * `GenusGSurface`          — ★★★ **Σ_g surface signature
                                  (parametric in genus)**: closes the
                                  §6 follow-up `signature(Σ_g) = (g, g)`
                                  for all g ≥ 0, with connected-sum
                                  additivity `Σ_{g+h} = Σ_g # Σ_h`.
                                  STRICT ∅-AXIOM.
    * `SurfaceComparisonTheorem` — ★★ **Comparison theorem**
                                  across 4 Kähler 2-folds (T²,
                                  ℙ², ℙ¹×ℙ¹, T²×T²): Hodge
                                  diamonds, Hodge Index Theorem
                                  formula `(1+2h^{2,0}, h^{1,1}-1)`,
                                  signature-vs-Hodge-structure
                                  coarseness witness

  ## T²ⁿ signature pattern

  Confirmed by the two ∅-axiom capstones above:

    `signature(H^n; T²ⁿ) = (½·C(2n, n), ½·C(2n, n))`

      n = 1:  (1, 1)   = (½·2, ½·2)
      n = 2:  (3, 3)   = (½·6, ½·6)
      n = 3:  (10, 10) predicted = (½·20, ½·20)

 
  exposition + open follow-ups.
-/
