import E213.Lib.Math.Cohomology.Surfaces.T2Minimal
import E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing
import E213.Lib.Math.Cohomology.Surfaces.T2Minimal.Signature
import E213.Lib.Math.Cohomology.Surfaces.T2Squared
import E213.Lib.Math.Cohomology.Surfaces.T2Squared.HardLefschetz

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Surfaces`.

  213-native CW models for low-dim Kähler manifolds — used to lift
  the ℤ/2-vacuous Hodge Index / Hodge-Riemann / Hard Lefschetz
  theorems to non-vacuous form (G10 Phase 2 follow-up).

  ## Sub-clusters

  ### `T2Minimal/` — 2-torus T² (real dim 2 = complex dim 1)

  · `T2Minimal.lean`     — 1 vertex + 2 edges + 1 face
  · `CupPairing.lean`    — symmetric cup `[[0,1],[1,0]]`
  · `Signature.lean`     — α₊, α₋ basis ⟹ signature (1, 1)

  ### `T2Squared/` — T² × T² (real dim 4 = complex dim 2)

  · `T2Squared.lean`         — Künneth product cells
                                (1+4+6+4+1 = 16 cells)
  · `HardLefschetz.lean`     — Kähler ω = a₁b₁ + a₂b₂;
                                L² : H⁰ → H⁴ mult-by-2;
                                L : H¹ → H³ 4×4 permutation
                                (det +1 ⟹ iso ℤ)
-/
