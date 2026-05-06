import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndex
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndexT2
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndexT2Squared
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndexP2
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndexP1Squared
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeRiemann
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeRiemannT2
import E213.Lib.Math.HodgeConjecture.Pairing.BalancedSignature
import E213.Lib.Math.HodgeConjecture.Pairing.HirzebruchMultiplicative
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndexGradeStructure
import E213.Lib.Math.HodgeConjecture.Pairing.KahlerGradeStructure
import E213.Lib.Math.HodgeConjecture.Pairing.SurfaceComparisonTheorem
import E213.Lib.Math.HodgeConjecture.Pairing.T2nPattern

/-! Spec-as-code entry point for `E213.Lib.Math.HodgeConjecture.Pairing`.

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
    * `T2nPattern`             — ★★ **Pattern theorem**:
                                  `signature(H^n; T²ⁿ) =
                                   (½·C(2n,n), ½·C(2n,n))`,
                                  bundling all n=1, n=2 witnesses
                                  + numerical sequence for n≤5
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

  See `research-notes/hodge/G12_T2_pattern.md` for the full
  exposition + open follow-ups.
-/
