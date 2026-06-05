import E213.Lib.Math.Geometry.GeometrizationConjecture.Ansatz
import E213.Lib.Math.Geometry.GeometrizationConjecture.M1Routes
import E213.Lib.Math.Geometry.GeometrizationConjecture.ScopeAndDepth
import E213.Lib.Math.Geometry.GeometrizationConjecture.DimSpectrum
import E213.Lib.Math.Geometry.GeometrizationConjecture.Poincare
import E213.Lib.Math.Geometry.GeometrizationConjecture.Ricci
import E213.Lib.Math.Geometry.GeometrizationConjecture.RicciFlow
import E213.Lib.Math.Geometry.GeometrizationConjecture.EightGeometries
import E213.Lib.Math.Geometry.GeometrizationConjecture.StructuralMapping
import E213.Lib.Math.Geometry.GeometrizationConjecture.Capstone
import E213.Lib.Math.Geometry.GeometrizationConjecture.Generalization
import E213.Lib.Math.Geometry.GeometrizationConjecture.JsjDeep
import E213.Lib.Math.Geometry.GeometrizationConjecture.MetricGeometries
import E213.Lib.Math.Geometry.GeometrizationConjecture.CrossFrame
import E213.Lib.Math.Geometry.GeometrizationConjecture.Exotic4Mfd
import E213.Lib.Math.Geometry.GeometrizationConjecture.KChartLensAbstract

/-! Spec-as-code entry point for `E213.Lib.Math.Geometry.GeometrizationConjecture`.

  R1 (CLOSED) — 213-Lens reading of Thurston/Perelman
  Geometrization conjecture + dimension-4 exotic anomaly.

  R1+ (PARTIAL) — Future-work partials advancing:
    · `Generalization.lean` — K_{NS,NT}^{(c)} parametric extended range 
    · `JsjDeep.lean` — JSJ 3-cell complex extension scaffold 
    · `MetricGeometries.lean` — E³/H³/H²×ℝ via mod-k Möbius P Lens family 

  Sub-tree organization (see `GeometrizationConjecture/INDEX.md`):

  ## Core (R1, CLOSED at 149 PURE / 0 DIRTY)

    · `Ansatz.lean`           — Steps 1-3 (core defs + M2 dual layers)
    · `M1Routes.lean`         — Steps 4, 5, 8 (atomicity + Möbius)
    · `ScopeAndDepth.lean`    — Steps 7, 9, 10 (cohomology depth filter)
    · `DimSpectrum.lean`      — Steps 6, 14 (chartBase ∈ {3..7} + Sym(3) capable)
    · `Poincare.lean`         — Steps 12, 13, 15 (Poincaré + Generalized + Filled)
    · `Ricci.lean`            — Steps 16, 17 (Ricci modulus, static)
    · `RicciFlow.lean`        — Ricci pillar CLOSED via A6 FLOW (coherentization
                                flow converges to canonical normal form, ∅-axiom)
    · `EightGeometries.lean`  — Steps 11, 18-22 (8 model geometries via Möbius P)
    · `StructuralMapping.lean`— Steps 21, 23, 24 (HC_K32 + universal-8 + ultimate)
    · `Capstone.lean`         — Step 25 (d=4 info richness + master + close certificate)

  ## R1+ Extensions (/partials)

    · `Generalization.lean`    — K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended 
    · `JsjDeep.lean`           — JSJ 3-cell complex Euler-target scaffold 
    · `MetricGeometries.lean`  — Mod-k Möbius P Lens family for E³/H³/H²×ℝ 

  All sub-files share `namespace E213.Lib.Math.Geometry.GeometrizationConjecture.ChartAxisAnsatz`
  for backwards-compatible theorem-name preservation.
-/
