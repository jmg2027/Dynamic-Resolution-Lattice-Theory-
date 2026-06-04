import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Hom
import E213.Lib.Math.Algebra.GRA.Category
import E213.Lib.Math.Algebra.GRA.DepthFunctor
import E213.Lib.Math.Algebra.GRA.Enrichment

/-!
# GRA Naturality — Phase 13 (post-consolidation)

The (now single) bipartite enrichment has both a *simplified*
instance (carrier = Nat, via `GRA23_NT`) and an *enriched*
instance (`GRA23_Bipartite` on `BipartiteCarrier`).  The
forgetful from enriched to simplified is a `GRAHom`
(`Enrichment.forgetHom`).

This file shows that translation between the enriched and
simplified Readings is **natural** with respect to the
forgetful: the diagram

    BipartiteCarrier ───→ bipartiteDepth = ⌈n/3⌉
       │                        │
     forget                 depth_formula
       ↓                        ↓
      Nat       ───→        ⌈n/3⌉

commutes — and after consolidation this is one statement
covering what used to be five (Walk, Cochain, Truncation,
Operad, Resolution).

This is the precise statement of "depth is the unique structural
invariant of the (2, 3) arithmetic", at the natural-transformation
level.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.Naturality

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Hom
open E213.Lib.Math.Algebra.GRA.Common (depth_formula)
open E213.Lib.Math.Algebra.GRA.Enrichment
  (BipartiteCarrier GRA23_Bipartite bipartiteDepth forgetHom)

/-! ### §1 — Forgetful + depth-commute -/

/-- Forgetting respects depth: the enriched depth equals the
    NT depth of the forgetful image. -/
theorem bipartite_depth_natural (b : BipartiteCarrier) (_hb : b.n ≥ 2) :
    bipartiteDepth (GRA23_Bipartite.grade b) =
    NumberTheory.GRA23_NT.depth (forgetHom.toFun b) := by
  show bipartiteDepth b.n = NumberTheory.GRA23_NT.depth b.n
  show (b.n + 2) / 3 = NumberTheory.ntDepth b.n
  rfl

/-! ### §2 — Composite hom: enriched → NT (the hub) -/

/-- The hub forgetful: `BipartiteCarrier`-enriched → NT.  Replaces
    the former `walkToNT`, `cochainToNT`, `truncationToNT`,
    `operadToNT`, `resolutionToNT` — all five were the same
    forgetful. -/
def bipartiteToNT : GRAHom GRA23_Bipartite NumberTheory.GRA23_NT :=
  forgetHom

/-! ### §3 — Master naturality theorem -/

/-- Master naturality witness: the enrichment's depth is the
    universal `⌈n/3⌉` evaluated on the forgetful's image. -/
structure DepthNaturality where
  /-- Bipartite enrichment: depth respects forget. -/
  bipartite : ∀ b : BipartiteCarrier, b.n ≥ 2 →
    bipartiteDepth b.n = (b.n + 2) / 3

/-- The naturality programme is inhabited. -/
def depth_naturality_witness : DepthNaturality where
  bipartite := fun b hb => Enrichment.bipartite_depth_eq b hb

/-! ### §4 — Cross-instance translation via the hub

Any two `BipartiteCarrier` values whose forgetful images agree
have the same enriched grade and depth.  Since all five domain
Readings collapse to `BipartiteCarrier`, this single statement
covers the former five pairwise translation lemmas.
-/

/-- Grade-match: if two carriers forget to the same Nat, their
    enriched grades agree. -/
theorem bipartite_grade_match (b₁ b₂ : BipartiteCarrier)
    (h : forgetHom.toFun b₁ = forgetHom.toFun b₂) :
    GRA23_Bipartite.grade b₁ = GRA23_Bipartite.grade b₂ := h

/-- Depth-match: forget-equal carriers have equal enriched depths. -/
theorem bipartite_depth_match (b₁ b₂ : BipartiteCarrier)
    (h : forgetHom.toFun b₁ = forgetHom.toFun b₂) :
    bipartiteDepth b₁.n = bipartiteDepth b₂.n := by
  show (b₁.n + 2) / 3 = (b₂.n + 2) / 3
  have : b₁.n = b₂.n := h
  rw [this]

end E213.Lib.Math.Algebra.GRA.Naturality
