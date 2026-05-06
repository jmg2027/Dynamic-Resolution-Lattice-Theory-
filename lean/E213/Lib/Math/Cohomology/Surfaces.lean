import E213.Lib.Math.Cohomology.Surfaces.T2Minimal
import E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing
import E213.Lib.Math.Cohomology.Surfaces.T2Minimal.Signature

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Surfaces`.

  213-native CW models for low-dimensional surfaces with non-trivial
  middle cohomology — used to lift the ℤ/2-vacuous Hodge Index /
  Hodge-Riemann theorems to non-vacuous form (G10 Phase 2 follow-up).

  ## Files

    * `T2Minimal/`
        - `T2Minimal.lean`     — 1 vertex + 2 edges (a, b) + 1 face;
                                 Int cochains C⁰/C¹/C² with all δ = 0
        - `CupPairing.lean`    — symmetric cup `[[0,1],[1,0]]`
        - `Signature.lean`     — α₊, α₋ basis with ±2 cup values
                                 ⟹ signature (1, 1)
-/
