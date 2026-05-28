import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Graph
import E213.Lib.Math.GRA.Analysis
import E213.Lib.Math.GRA.Cohomology
import E213.Lib.Math.GRA.HoTT
import E213.Lib.Math.GRA.HigherAlgebra
import E213.Lib.Math.GRA.Translation
import E213.Lib.Math.GRA.Category
import E213.Lib.Math.GRA.Groupoid
import E213.Lib.Math.GRA.Hom
import E213.Lib.Math.GRA.DepthFunctor
import E213.Lib.Math.GRA.WalkEnrichment
import E213.Lib.Math.GRA.CochainEnrichment
import E213.Lib.Math.GRA.HoTTEnrichment
import E213.Lib.Math.GRA.HigherAlgebraEnrichment
import E213.Lib.Math.GRA.AnalysisEnrichment
import E213.Lib.Math.GRA.Naturality
import E213.Lib.Math.GRA.SectionRetraction
import E213.Lib.Math.GRA.Monoidal
import E213.Lib.Math.GRA.LensBridge

/-! # GRA (Graded Residue Arithmetic) — umbrella

Marathon 16 (closed): the universal (2,3)-graded meta-structure of 213.

  ## Phases 1–6 — Universality + Translation

  * `GRAModel`        — 7-axiom typeclass + `GRAIso` refl/symm/trans
  * `Common`          — shared PURE Nat arithmetic (coprime, reach,
                        depth formula, depth comparison)
  * `NumberTheory`    — hub instance on ℕ
  * `Graph`           — R₄ walk-length reading + iso to NT
  * `Analysis`        — R₅ resolution-exponent reading + iso to NT
  * `Cohomology`      — R₁ cochain-degree reading + iso to NT
  * `HoTT`            — R₃ truncation-level reading + iso to NT
  * `HigherAlgebra`   — R₂ operad-level reading + iso + universality capstone
  * `Translation`     — 5-way master translation + universal depth prediction

  ## Phases 7–11 — Category theory

  * `Category`        — 213-native `Cat`-typeclass, `GRACat`,
                        `ReadingCat` (6 closed (2,3)-models +
                        connectedness witness)
  * `Groupoid`        — every `GRAIso` is invertible; connected
                        groupoid structure on `ReadingCat`;
                        `Reading.hubAtNT` witnesses hub-and-spoke
  * `Hom`             — `GRAHom` (more general than iso),
                        category laws, forgetful `GRAIso → GRAHom`
  * `DepthFunctor`    — `(2,3)`-depth is a **constant functor** on
                        `ReadingCat`; `Reading_depth_const` proves
                        all 6 Readings agree on `⌈n/3⌉`
  * `WalkEnrichment`  — concrete carrier enrichment for R₄:
                        `EdgeWalk` with bipartite length constraint
                        + `forgetHom : EdgeWalk → Nat`

  ## Phases 12–15 — Full enrichment + naturality + retraction + monoidal

  * `CochainEnrichment`           — R₁ (degree) enrichment
  * `HoTTEnrichment`              — R₃ (truncation) enrichment
  * `HigherAlgebraEnrichment`     — R₂ (operad level) enrichment
  * `AnalysisEnrichment`          — R₅ (resolution exponent) enrichment
  * `Naturality`                  — translation between enrichments is
                                    natural with respect to the forgetful;
                                    `DepthNaturality` capstone bundles
                                    depth-preservation for all 5 enrichments
  * `SectionRetraction`           — each forgetful has a section on its
                                    valid image (`n = 0 ∨ n ≥ 2`);
                                    `WalkRetract` structures up the data
  * `Monoidal`                    — `product : GRAModel → GRAModel →
                                    GRAModel`, the (2, 3)-monoidal product;
                                    `trivial23` as the unit; `leftUnitHom`
                                    and `rightUnitHom` as the unit isos

  ## Phase 16 — Lens bridge (Cat / HoTT as Readings)

  * `LensBridge`                  — `Raw.fold 2 3 (· + ·)` as the
                                    canonical Raw → Nat grade map;
                                    all five enrichment grade maps are
                                    definitionally equal to it.
                                    `truncation_operad_grade_agree` is
                                    the HoTT ↔ Higher Algebra Lens-level
                                    equation: HoTT's truncation hierarchy
                                    and the `E_n` ladder project to the
                                    same Raw-level kernel.

Narrative: `theory/math/gra_book.md`, `theory/math/graded_residue_arithmetic.md`,
`theory/essays/gra_as_substrate_of_cat_hott.md`.
**Strict ∅-axiom: 296 PURE / 0 DIRTY** (118 from Phases 1–6 + 49
from Phases 7–11 + 92 from Phases 12–15 + 37 from Phase 16).  `ax_coprime` uses `gcd213`
(PURE) rather than Lean-core `Nat.gcd`.  Every proof uses kernel-decide,
`rfl`, or explicit Nat / `Meta.Nat.NatDiv213` / `Meta.Nat.AddMod213`
lemmas — no `omega`, no `simp`-driven rewrites, no Mathlib, no `Classical`.
-/
