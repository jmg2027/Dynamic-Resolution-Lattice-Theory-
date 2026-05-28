import E213.Theory.Raw.API
import E213.Lib.Math.GRA.Enrichment

/-!
# GRA Lens Bridge — Phase 16

The five GRA enrichments (Walk, Cochain, Truncation, Operad,
Resolution) — now consolidated as the single `BipartiteCarrier`
enrichment — are Readings of the same `(2, 3)`-arithmetic forced
by atomic distinguishing.  This file connects them to the
213-native catamorphism `Raw.fold` (the infrastructure underlying
`E213.Lens.SemanticAtom.universalMorphism`):

  * The **canonical Nat-level grade map**
    `canonicalGradeMap := Raw.fold 2 3 (· + ·)` is the
    Raw → Nat function forced by `(NS, NT) = (3, 2)`.
  * The natural Raw → BipartiteCarrier → Nat composite equals
    `canonicalGradeMap` (factoring through the `.n` projection).
  * Hence the (one parametric) enrichment sends
    `Raw.a ↦ 2`, `Raw.b ↦ 3`, and acts *grade-additively* on
    `Raw.slash`.

We use `Raw.fold` with the Nat-level `(· + ·)` rather than the
enriched `.combine`.  Both yield the same arithmetic; the Nat-
level form is PURE (no `propext` from typeclass plumbing or
`Prop`-field structure equality).

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.LensBridge

open E213.Theory
open E213.Lib.Math.GRA.Enrichment (BipartiteCarrier)

/-! ### §1 — Canonical Nat-level grade map -/

/-- The canonical Raw → Nat grade map: `Raw.fold 2 3 (· + ·)`.
    `Raw.a ↦ 2`, `Raw.b ↦ 3`, `Raw.slash x y ↦ grade x + grade y`.
    This is the (2, 3)-arithmetic at the Raw level, forced by
    atomic distinguishing. -/
def canonicalGradeMap : Raw → Nat := Raw.fold 2 3 (· + ·)

theorem canonicalGradeMap_a : canonicalGradeMap Raw.a = 2 := rfl
theorem canonicalGradeMap_b : canonicalGradeMap Raw.b = 3 := rfl

theorem canonicalGradeMap_slash (x y : Raw) (h : x ≠ y) :
    canonicalGradeMap (Raw.slash x y h) =
    canonicalGradeMap x + canonicalGradeMap y :=
  Raw.fold_slash 2 3 (· + ·) Nat.add_comm x y h

/-! ### §2 — Bipartite enrichment grade map (≡ canonicalGradeMap)

In the pre-consolidation marathon, this section defined five
copies of `canonicalGradeMap` (one per Reading), each
definitionally equal to `canonicalGradeMap`.  After consolidation
there is **one** enriched grade map — equal to `canonicalGradeMap`
by definitional unfolding.
-/

/-- The bipartite enrichment's Raw → Nat grade map — identical to
    `canonicalGradeMap`.  All five domain Readings (Walk /
    Cochain / Truncation / Operad / Resolution) project through
    `BipartiteCarrier.n` to this same function. -/
def bipartiteGradeMap : Raw → Nat := canonicalGradeMap

theorem bipartiteGradeMap_a : bipartiteGradeMap Raw.a = 2 := rfl
theorem bipartiteGradeMap_b : bipartiteGradeMap Raw.b = 3 := rfl

theorem bipartiteGradeMap_slash (x y : Raw) (h : x ≠ y) :
    bipartiteGradeMap (Raw.slash x y h) =
    bipartiteGradeMap x + bipartiteGradeMap y :=
  canonicalGradeMap_slash x y h

/-- The bipartite enrichment grade map agrees with the canonical
    grade map pointwise (by `rfl`).  This is the strongest formal
    expression of "the five Readings are one arithmetic". -/
theorem bipartite_canonical_agree (r : Raw) :
    bipartiteGradeMap r = canonicalGradeMap r := rfl

/-! ### §3 — Carrier-level realization at atoms

The `Raw.fold` lifted into the enriched carrier sends atoms to
the corresponding bipartite carrier elements (n = 2 / n = 3).
After consolidation, the five domain-flavoured versions
(`walk_realize_a`, `cochain_realize_a`, …) become one statement
about `BipartiteCarrier`.
-/

/-- Atom realization at `a`: `Raw.fold` into `BipartiteCarrier`
    sends `Raw.a` to the n = 2 carrier element. -/
theorem bipartite_realize_a :
    (Raw.fold BipartiteCarrier.two BipartiteCarrier.three
              BipartiteCarrier.combine Raw.a).n = 2 := rfl

/-- Atom realization at `b`: sends `Raw.b` to the n = 3 element. -/
theorem bipartite_realize_b :
    (Raw.fold BipartiteCarrier.two BipartiteCarrier.three
              BipartiteCarrier.combine Raw.b).n = 3 := rfl

end E213.Lib.Math.GRA.LensBridge
