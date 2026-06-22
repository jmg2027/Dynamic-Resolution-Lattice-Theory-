import E213.Lens.LensCore
import E213.Lens.Foundations.SemanticAtom
import E213.Lens.Foundations.Initiality
import E213.Lens.Lattice.Chain
import E213.Lens.Lattice.Preorder

/-!
# Lens ring: Public API (Tier 1 — core surface)

Single-import entry point for the Lens framework Tier 1 public
API.  Pattern follows `Theory/Raw.lean` precedent.

**Tier 1 (this shim, bundled)** — the three core hypervisor
classes (HV1 + HV2 + HV3):

**HV1 — Type API**: Lens type + catamorphism
  - `Lens (α : Type)` — structure `{base_a, base_b, combine}`
  - `Lens.view : Lens α → Raw → α`
  - `Lens.{leaves, depth}` — canonical Lenses

**HV2 — Equivalence API**: Lens-induced equality + refinement
  - `Lens.equiv`, `Lens.equiv_{refl, symm, trans}`
  - `Lens.refines`, `Lens.refines_{refl, trans}`
  - `Refines.Chain`, `Refines.Preorder`

**HV3 — Initiality API**: universal property of Raw → α
  - `Lens.view_unique` — uniqueness up to commutative-Raw-algebra
  - `SemanticAtom.{HasDistinguishing, Raw.instHasDistinguishing}`

## Tier 2 (NOT bundled — import the dedicated aggregators)

**HV4 — Lattice API** (`import E213.Lens.Lattice`):
  - `joinLens`, `prodLens` (join + meet)
  - `joinLens_{kernel, is_least}`
  - `Lattice.{FamilyJoin, FamilyMeet, IndexedJoin, JoinEquiv}`

**HV5 — Composition API** (`import E213.Lens.Compose`):
  - `Compose.Factoring.factors_through_implies_refines`
  - `Compose.{ImageMinimum, OnLens}`

**HV6 — Canonical Form API** (`import E213.Lens.Universal`):
  - `Universal.Flat.every_lens_factors_through_idLens`
  - `Universal.QuotLens.universalLens`
  - `Properties.CanonicalForm.lens_canonical_universal`
  - `Universal.Witnesses.*` — concrete universal-Lens witnesses
    at Nat2/3/4, Q213, Q213³

## Optional (NOT bundled — import individually)

  - HV7 = `Lens/Instances/*` (catalog of 30+ concrete Lenses)
  - HV8 = `Lens/Characterisation/*` (refines-relation catalog)
  - `Lens/Algebra/{FreeAudit, FourDistinct, ...}` — internal,
    supporting infra for HV3/HV6, not consumed directly

## Layered position

  - **Imports**: Theory (Raw API).  No upward imports — Lens ring
    is the catamorphism layer, consumed by Lib.

## Axiom status

`Lens.view`, `Lens.view_unique`, and the universalLens construction
are PURE (∅-axiom).  The production critical path is ∅-axiom on the
whole tree (per `STRICT_ZERO_AXIOM.md` audit).  Module-by-module
status is recorded inline in each sub-cluster umbrella.

## Tier 1/2 split rationale

Tier 1 (HV1–HV3) is the always-needed kernel any Lens consumer
imports.  Tier 2 (HV4–HV6) covers the lattice / compose / canonical-
form algebras — useful but not always needed; importing them
on-demand via `Lens.{Lattice, Compose, Universal}` keeps the
common-import surface narrow.
-/
