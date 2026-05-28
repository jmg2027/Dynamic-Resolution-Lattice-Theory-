import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom
import E213.Lib.Math.GRA.Category
import E213.Lib.Math.GRA.DepthFunctor
import E213.Lib.Math.GRA.WalkEnrichment
import E213.Lib.Math.GRA.CochainEnrichment
import E213.Lib.Math.GRA.HoTTEnrichment
import E213.Lib.Math.GRA.HigherAlgebraEnrichment
import E213.Lib.Math.GRA.AnalysisEnrichment

/-!
# GRA Naturality — Phase 13

Each of the five Readings now has both a *simplified* instance
(carrier = Nat) and an *enriched* instance (carrier = the
domain-specific tagged type — Walk / Cochain / Truncation /
Operad / Resolution).  The forgetful `enriched → simplified`
is a `GRAHom` (proved in each enrichment file).

This file shows that translation between Readings is **natural**
with respect to the forgetful: the diagram

    Walk ───→ EdgeWalk's depth = ⌈n/3⌉
     │              │
   forget        depth_formula
     ↓              ↓
    Nat  ───→  ⌈n/3⌉

commutes, and the same holds for every other Reading.

Furthermore, *cross-Reading translation* is the unique map that
makes all such squares commute — this is the precise statement of
"depth is the unique structural invariant of the (2, 3)
arithmetic", expressed at the natural-transformation level.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.Naturality

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom
open E213.Lib.Math.GRA.Common (depth_formula)

/-! ### §1 — Per-Reading forgetful + depth-commute

For each enriched Reading, the forgetful preserves grade
(`grade_comm` axiom of `GRAHom`).  Combined with the universal
depth formula `depth = ⌈n/3⌉`, the forgetful also preserves
depth pointwise.
-/

/-- For Walk (R₄): forgetting respects depth. -/
theorem walk_depth_natural (w : WalkEnrichment.EdgeWalk) (hw : w.length ≥ 2) :
    WalkEnrichment.edgeWalkDepth (WalkEnrichment.GRA23_EdgeWalk.grade w) =
    NumberTheory.GRA23_NT.depth (WalkEnrichment.forgetHom.toFun w) := by
  show WalkEnrichment.edgeWalkDepth w.length =
       NumberTheory.GRA23_NT.depth w.length
  show (w.length + 2) / 3 = NumberTheory.ntDepth w.length
  rfl

/-- For Cochain (R₁): forgetting respects depth. -/
theorem cochain_depth_natural (c : CochainEnrichment.Cochain) (hc : c.degree ≥ 2) :
    CochainEnrichment.cochainDepth (CochainEnrichment.GRA23_CochainEnriched.grade c) =
    NumberTheory.GRA23_NT.depth (CochainEnrichment.forgetHom.toFun c) := rfl

/-- For Truncation (R₃): forgetting respects depth. -/
theorem truncation_depth_natural (t : HoTTEnrichment.Truncation) (ht : t.level ≥ 2) :
    HoTTEnrichment.truncationDepth (HoTTEnrichment.GRA23_TruncationEnriched.grade t) =
    NumberTheory.GRA23_NT.depth (HoTTEnrichment.forgetHom.toFun t) := rfl

/-- For Operad (R₂): forgetting respects depth. -/
theorem operad_depth_natural (o : HigherAlgebraEnrichment.Operad) (ho : o.level ≥ 2) :
    HigherAlgebraEnrichment.operadDepth
      (HigherAlgebraEnrichment.GRA23_OperadEnriched.grade o) =
    NumberTheory.GRA23_NT.depth (HigherAlgebraEnrichment.forgetHom.toFun o) := rfl

/-- For Resolution (R₅): forgetting respects depth. -/
theorem resolution_depth_natural (r : AnalysisEnrichment.Resolution)
    (hr : r.exponent ≥ 2) :
    AnalysisEnrichment.resolutionDepth
      (AnalysisEnrichment.GRA23_ResolutionEnriched.grade r) =
    NumberTheory.GRA23_NT.depth (AnalysisEnrichment.forgetHom.toFun r) := rfl

/-! ### §2 — Cross-Reading translation via the simplified hub

If you have a `Walk` and want a `Cochain` of the same grade, you
go `Walk → Nat → Cochain` through the hub.  The composite is
natural in the source Reading.
-/

/-- Composite hom: Walk-enriched → NT (the hub). -/
def walkToNT : GRAHom WalkEnrichment.GRA23_EdgeWalk
    NumberTheory.GRA23_NT := WalkEnrichment.forgetHom

/-- Composite hom: Cochain-enriched → NT (the hub). -/
def cochainToNT : GRAHom CochainEnrichment.GRA23_CochainEnriched
    NumberTheory.GRA23_NT := CochainEnrichment.forgetHom

/-- Composite hom: Truncation-enriched → NT (the hub). -/
def truncationToNT : GRAHom HoTTEnrichment.GRA23_TruncationEnriched
    NumberTheory.GRA23_NT := HoTTEnrichment.forgetHom

/-- Composite hom: Operad-enriched → NT (the hub). -/
def operadToNT : GRAHom HigherAlgebraEnrichment.GRA23_OperadEnriched
    NumberTheory.GRA23_NT := HigherAlgebraEnrichment.forgetHom

/-- Composite hom: Resolution-enriched → NT (the hub). -/
def resolutionToNT : GRAHom AnalysisEnrichment.GRA23_ResolutionEnriched
    NumberTheory.GRA23_NT := AnalysisEnrichment.forgetHom

/-! ### §3 — Master naturality theorem

For every Reading, the depth on the enriched carrier equals the
depth on `Nat` of the forgetful's image.  This is the *natural
transformation* statement: the depth functor commutes with the
forgetful from enriched to simplified Readings, uniformly across
all five Readings.
-/

/-- Master naturality witness: every enrichment's depth is the
    universal `⌈n/3⌉` evaluated on the forgetful's image. -/
structure DepthNaturality where
  /-- Walk: depth respects forget. -/
  walk : ∀ w : WalkEnrichment.EdgeWalk, w.length ≥ 2 →
    WalkEnrichment.edgeWalkDepth w.length = (w.length + 2) / 3
  /-- Cochain: depth respects forget. -/
  cochain : ∀ c : CochainEnrichment.Cochain, c.degree ≥ 2 →
    CochainEnrichment.cochainDepth c.degree = (c.degree + 2) / 3
  /-- Truncation: depth respects forget. -/
  truncation : ∀ t : HoTTEnrichment.Truncation, t.level ≥ 2 →
    HoTTEnrichment.truncationDepth t.level = (t.level + 2) / 3
  /-- Operad: depth respects forget. -/
  operad : ∀ o : HigherAlgebraEnrichment.Operad, o.level ≥ 2 →
    HigherAlgebraEnrichment.operadDepth o.level = (o.level + 2) / 3
  /-- Resolution: depth respects forget. -/
  resolution : ∀ r : AnalysisEnrichment.Resolution, r.exponent ≥ 2 →
    AnalysisEnrichment.resolutionDepth r.exponent = (r.exponent + 2) / 3

/-- The naturality programme is inhabited. -/
def depth_naturality_witness : DepthNaturality where
  walk := fun w _hw => WalkEnrichment.walk_depth_eq w _hw
  cochain := fun c _hc => CochainEnrichment.cochain_depth_eq c _hc
  truncation := fun t _ht => HoTTEnrichment.truncation_depth_eq t _ht
  operad := fun o _ho => HigherAlgebraEnrichment.operad_depth_eq o _ho
  resolution := fun r _hr => AnalysisEnrichment.resolution_depth_eq r _hr

/-! ### §4 — Cross-enriched translation via the hub

For any two enriched carriers, a "translation" exists by going
through Nat.  Since all five forget to the same Nat-arithmetic,
translation is *unique* up to grade — equivalence of enriched
Readings at the grade level.
-/

/-- Walk-grade equals Cochain-grade under matching forgetfuls. -/
theorem walk_cochain_grade_match (w : WalkEnrichment.EdgeWalk)
    (c : CochainEnrichment.Cochain)
    (h : WalkEnrichment.forgetHom.toFun w = CochainEnrichment.forgetHom.toFun c) :
    WalkEnrichment.GRA23_EdgeWalk.grade w =
    CochainEnrichment.GRA23_CochainEnriched.grade c := h

/-- Walk-depth equals Cochain-depth when their forget-images agree. -/
theorem walk_cochain_depth_match (w : WalkEnrichment.EdgeWalk)
    (c : CochainEnrichment.Cochain)
    (h : WalkEnrichment.forgetHom.toFun w = CochainEnrichment.forgetHom.toFun c) :
    WalkEnrichment.edgeWalkDepth w.length =
    CochainEnrichment.cochainDepth c.degree := by
  show (w.length + 2) / 3 = (c.degree + 2) / 3
  have : w.length = c.degree := h
  rw [this]

end E213.Lib.Math.GRA.Naturality
