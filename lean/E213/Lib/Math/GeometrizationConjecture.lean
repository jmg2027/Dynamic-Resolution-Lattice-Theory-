import E213.Lib.Math.GeometrizationConjecture.Ansatz
import E213.Lib.Math.GeometrizationConjecture.M1Routes
import E213.Lib.Math.GeometrizationConjecture.ScopeAndDepth
import E213.Lib.Math.GeometrizationConjecture.DimSpectrum
import E213.Lib.Math.GeometrizationConjecture.Poincare
import E213.Lib.Math.GeometrizationConjecture.Ricci
import E213.Lib.Math.GeometrizationConjecture.EightGeometries
import E213.Lib.Math.GeometrizationConjecture.StructuralMapping
import E213.Lib.Math.GeometrizationConjecture.Capstone
import E213.Lib.Math.GeometrizationConjecture.Generalization
import E213.Lib.Math.GeometrizationConjecture.JsjDeep
import E213.Lib.Math.GeometrizationConjecture.MetricGeometries
import E213.Lib.Math.GeometrizationConjecture.CrossFrame
import E213.Lib.Math.GeometrizationConjecture.Exotic4Mfd

/-! Spec-as-code entry point for `E213.Lib.Math.GeometrizationConjecture`.

  G121 R1 (CLOSED) — 213-Lens reading of Thurston/Perelman
  Geometrization conjecture + dimension-4 exotic anomaly.

  G121 R1+ (PARTIAL) — Future-work partials advancing G123/G124/G125:
    · `Generalization.lean` — K_{NS,NT}^{(c)} parametric extended range (G124)
    · `JsjDeep.lean` — JSJ 3-cell complex extension scaffold (G123)
    · `MetricGeometries.lean` — E³/H³/H²×ℝ via mod-k Möbius P Lens family (G125)

  Sub-tree organization (see `GeometrizationConjecture/INDEX.md`):

  ## Core (G121 R1, CLOSED at 149 PURE / 0 DIRTY)

    · `Ansatz.lean`           — Steps 1-3 (core defs + M2 dual layers)
    · `M1Routes.lean`         — Steps 4, 5, 8 (atomicity + Möbius)
    · `ScopeAndDepth.lean`    — Steps 7, 9, 10 (cohomology depth filter)
    · `DimSpectrum.lean`      — Steps 6, 14 (chartBase ∈ {3..7} + Sym(3) capable)
    · `Poincare.lean`         — Steps 12, 13, 15 (Poincaré + Generalized + Filled)
    · `Ricci.lean`            — Steps 16, 17 (Ricci modulus)
    · `EightGeometries.lean`  — Steps 11, 18-22 (8 model geometries via Möbius P)
    · `StructuralMapping.lean`— Steps 21, 23, 24 (HC_K32 + universal-8 + ultimate)
    · `Capstone.lean`         — Step 25 (d=4 info richness + master + close certificate)

  ## R1+ Extensions (G123/G124/G125 partials)

    · `Generalization.lean`    — K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended (G124)
    · `JsjDeep.lean`           — JSJ 3-cell complex Euler-target scaffold (G123)
    · `MetricGeometries.lean`  — Mod-k Möbius P Lens family for E³/H³/H²×ℝ (G125)

  All sub-files share `namespace E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz`
  for backwards-compatible theorem-name preservation.
-/
