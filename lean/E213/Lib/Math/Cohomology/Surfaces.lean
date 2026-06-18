import E213.Lib.Math.Cohomology.Surfaces.T2Minimal
import E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing
import E213.Lib.Math.Cohomology.Surfaces.T2Minimal.Signature
import E213.Lib.Math.Cohomology.Surfaces.T2Squared
import E213.Lib.Math.Cohomology.Surfaces.T2Squared.HodgeIndex
import E213.Lib.Math.Cohomology.Surfaces.T2nBetti
import E213.Lib.Math.Cohomology.Surfaces.P2Minimal
import E213.Lib.Math.Cohomology.Surfaces.P1Squared
import E213.Lib.Math.Cohomology.Surfaces.AbelianSurfaceHodge

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Surfaces`.

  213-native CW models for low-dim Kähler manifolds — used to lift
  the ℤ/2-vacuous Hodge Index / Hodge-Riemann / Hard Lefschetz
  theorems to non-vacuous form (Phase 2 follow-up).

  ## Sub-clusters

  ### `T2Minimal/` — 2-torus T² (real dim 2 = complex dim 1)

  · `T2Minimal.lean`     — 1 vertex + 2 edges + 1 face
  · `CupPairing.lean`    — symmetric cup `[[0,1],[1,0]]`
  · `Signature.lean`     — α₊, α₋ basis ⟹ signature (1, 1)

  ### `T2Squared/` — T² × T² (real dim 4 = complex dim 2)

  · `T2Squared.lean`         — Künneth product cells
                                (1+4+6+4+1 = 16 cells)
  · `HodgeIndex.lean`        — cup C² × C² → C⁴; 3 hyperbolic
                                blocks ⟹ signature (3, 3)

  ### `P2Minimal/` — complex projective plane ℙ² (rank 1 ρ)

  · `P2Minimal.lean`         — 1 pt + 1 line + 1 plane
                                (h^{2,0}=0, h^{1,1}=1);
                                cup `[H ⌣ H = 1]` ⟹ signature (1, 0)

  ### `P1Squared/` — ℙ¹ × ℙ¹ (rational surface, ρ = 2)

  · `P1Squared.lean`         — 1 pt + 2 lines (H₁, H₂) + 1 vol
                                (h^{2,0}=0, h^{1,1}=2); cup
                                `[[0,1],[1,0]]` ⟹ signature (1, 1)
                                — same matrix + signature as T²
                                **but distinct Hodge structure**.
-/
