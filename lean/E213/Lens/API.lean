import E213.LensCore
import E213.Lens.SemanticAtom
import E213.Lens.Initiality
import E213.Lens.Lattice.Lattice
import E213.Lens.Lattice.Join
import E213.Lens.Lattice.Meet
import E213.Lens.Lattice.FamilyJoin
import E213.Lens.Lattice.FamilyMeet
import E213.Lens.Lattice.IndexedJoin
import E213.Lens.Lattice.JoinEquiv
import E213.Lens.Compose.Factoring
import E213.Lens.Compose.ImageMinimum
import E213.Lens.Compose.OnLens
import E213.Lens.Universal.Flat
import E213.Lens.Universal.QuotLens
import E213.Lens.Properties.CanonicalForm
import E213.Lens.Refines.Chain
import E213.Lens.Refines.Preorder

/-!
# Hypervisor: Public API (re-export shim)

G12 D3: single-import entry point for the Hypervisor (Lens framework)
public API.  Pattern follows `Firmware/Raw.lean` precedent.

Downstream code can `import E213.Lens.API` and access the
6-category public surface (HV1–HV6 in G12 §4.1 classification):

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
  - `Universal.Flat.every_lens_factors_through_idLens`

**HV4 — Lattice API**: refines preorder lattice structure
  - `joinLens`, `prodLens` (join + meet)
  - `joinLens_{kernel, is_least}`
  - `Lattice.{FamilyJoin, FamilyMeet, IndexedJoin, JoinEquiv}`

**HV5 — Composition API**: Lens factoring + image
  - `Compose.Factoring.factors_through_implies_refines`
  - `Compose.{ImageMinimum, OnLens}`

**HV6 — Canonical Form API**: universalLens construction
  - `Universal.QuotLens.universalLens`
  - `Properties.CanonicalForm.universalLens_recovers`

**Optional (NOT bundled in this shim)**:
  - HV7 = `Hypervisor/Lens/Instances/*` (catalog of 25+ concrete
    Lenses) — import individually as needed
  - HV8 = `Hypervisor/Lens/Characterisation/*` (refines-relation
    catalog) — import individually as needed
  - `Lens/Kernel/{FreeAudit, FourDistinct, ...}` — internal,
    supporting infra for HV3/HV6, not consumed directly

**Imports**: Firmware (Raw API).  No upward imports — Hypervisor
is the catamorphism layer, consumed by Meta and App.

**Axiom status**: `Lens.view`, `Lens.view_unique`, and the
universalLens construction are PURE (∅-axiom).  Some lattice and
characterisation theorems inherit ≤ {propext, Quot.sound} from
their underlying decidability machinery.

See `research-notes/G12_layered_api_classification.md` §4 for the
rigorous public-API classification.
-/
