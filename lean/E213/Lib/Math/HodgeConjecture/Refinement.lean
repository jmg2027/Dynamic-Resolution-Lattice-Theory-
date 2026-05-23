import E213.Lib.Math.HodgeConjecture.Refinement.CupAtomicGeneration
import E213.Lib.Math.HodgeConjecture.Refinement.CupAtomicGenerationDelta3
import E213.Lib.Math.HodgeConjecture.Refinement.CupAtomicGenerationDelta5
import E213.Lib.Math.HodgeConjecture.Refinement.CupAtomicGenerationGrid
import E213.Lib.Math.HodgeConjecture.Refinement.GeneralizedHodge
import E213.Lib.Math.HodgeConjecture.Refinement.LefschetzHyperplane
import E213.Lib.Math.HodgeConjecture.Refinement.LefschetzOneOne
import E213.Lib.Math.HodgeConjecture.Refinement.StandardConjectures
import E213.Lib.Math.HodgeConjecture.Refinement.Voisin

/-! Spec-as-code entry point for `E213.Lib.Math.HodgeConjecture.Refinement`.

  Refinements + neighbouring conjectures clarifying the
  Hodge-conjecture statement.

  ## Files

    * `LefschetzOneOne`            — Lefschetz (1,1) theorem
    * `LefschetzHyperplane`        — Lefschetz hyperplane theorem
    * `GeneralizedHodge`           — generalised Hodge conjecture
    * `StandardConjectures`        — Grothendieck's standard
                                     conjectures (cross-reference)
    * `CupAtomicGeneration`        — cup-atomic generation at Δ⁴
                                     (5 vertices → 10 edges)
    * `CupAtomicGenerationDelta3`  — sister closure at Δ³
                                     (4 vertices → 6 edges)
    * `CupAtomicGenerationDelta5`  — sister closure at Δ⁵
                                     (6 vertices → 15 edges)
    * `CupAtomicGenerationGrid`    — unified Δ³ + Δ⁴ + Δ⁵
                                     HC²¹³ automation master
    * `Voisin`                     — Voisin's counterexample
                                     machinery
-/
