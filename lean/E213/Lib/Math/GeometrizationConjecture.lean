import E213.Lib.Math.GeometrizationConjecture.Ansatz
import E213.Lib.Math.GeometrizationConjecture.M1Routes
import E213.Lib.Math.GeometrizationConjecture.ScopeAndDepth
import E213.Lib.Math.GeometrizationConjecture.DimSpectrum
import E213.Lib.Math.GeometrizationConjecture.Poincare
import E213.Lib.Math.GeometrizationConjecture.Ricci
import E213.Lib.Math.GeometrizationConjecture.EightGeometries
import E213.Lib.Math.GeometrizationConjecture.StructuralMapping
import E213.Lib.Math.GeometrizationConjecture.Capstone

/-! Spec-as-code entry point for `E213.Lib.Math.GeometrizationConjecture`.

  G121 R1 — 213-Lens reading of the Thurston/Perelman Geometrization
  conjecture and the dimension-4 exotic-smoothness anomaly.

  Sub-tree organization (see `GeometrizationConjecture/INDEX.md`):

    · `Ansatz.lean`           — Steps 1-3 (core defs + M2 dual layers)
    · `M1Routes.lean`         — Steps 4, 5, 8 (atomicity + Möbius)
    · `ScopeAndDepth.lean`    — Steps 7, 9, 10 (cohomology depth filter)
    · `DimSpectrum.lean`      — Steps 6, 14 (chartBase ∈ {3..7} + Sym(3) capable)
    · `Poincare.lean`         — Steps 12, 13, 15 (Poincaré + Generalized + Filled)
    · `Ricci.lean`            — Steps 16, 17 (Ricci modulus)
    · `EightGeometries.lean`  — Steps 11, 18-22 (8 model geometries via Möbius P)
    · `StructuralMapping.lean`— Steps 21, 23, 24 (HC_K32 + universal-8 + ultimate)
    · `Capstone.lean`         — Step 25 (d=4 info richness + master + close certificate)

  All sub-files share the `namespace E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz`
  for backwards-compatible theorem-name preservation across the
  pre-split (single-file) → post-split (9-file sub-tree) refactor.

  ## Cross-references

    · `research-notes/G121_dim4_self_pointing_axis.md` — full narrative
      + open knots M1-M4 + validation routes R1-R4 + close certificate
    · `lean/E213/Lib/Math/BipartiteDecomp/G44Capstone.lean` —
      substrate_sum (chartBase 3 2 = 5 numerical agreement)
    · `lean/E213/Lib/Physics/Symmetry/C3ChainCapstone.lean` —
      Sym(3) gauge structure on K_{3,2}^{(c=2)}

  **G121 R1 — CLOSED at 149 PURE / 0 DIRTY across 25 steps.**
-/
