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
                        + `forgetHom : EdgeWalk → Nat` showing
                        the simplified Reading is the image of the
                        enriched one

Narrative: `theory/math/gra_book.md`, `theory/math/graded_residue_arithmetic.md`.
**Strict ∅-axiom: 167 PURE / 0 DIRTY** (118 from Phases 1–6 + 49
from Phases 7–11).  `ax_coprime` uses `gcd213` (PURE) rather than
Lean-core `Nat.gcd`.  Every proof uses kernel-decide, `rfl`, or
explicit Nat / `Meta.Nat.NatDiv213` / `Meta.Nat.AddMod213` lemmas
— no `omega`, no `simp`-driven rewrites, no Mathlib, no `Classical`.
-/
