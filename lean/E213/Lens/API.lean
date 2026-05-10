import E213.Lens.LensCore
import E213.Lens.SemanticAtom
import E213.Lens.Initiality
import E213.Lens.Lattice.Lattice
import E213.Lens.Lattice.Meet
import E213.Lens.Lattice.IndexedJoin
import E213.Lens.Lattice.JoinEquiv
import E213.Lens.Compose.Factoring
import E213.Lens.Compose.ImageMinimum
import E213.Lens.Compose.OnLens
import E213.Lens.Universal.Flat
import E213.Lens.Refines.Chain
import E213.Lens.Refines.Preorder
import E213.Lens.EqPW

/-!
# Hypervisor: Public API (re-export shim)

Single-import entry point for the Hypervisor (Lens framework) public
API.  Pattern follows `Firmware/Raw.lean` precedent.

**Removed**: the Prop-codomain `universalLens` construction +
`joinLens` / `Lattice.Join` / `Lattice.FamilyJoin` / `Lattice.FamilyMeet`
/ `Properties.CanonicalForm` chain — under the
"design-by-funext/propext 금지" directive, all Lens (Raw → Prop)
constructions were deleted (their equalities require propext).

The remaining lattice content (Meet, IndexedJoin) is PURE.

**Categories (PURE)**:

  HV1 — Type API: Lens type + catamorphism
  HV2 — Equivalence API: equiv / refines
  HV3 — Initiality API: view_unique, HasDistinguishing,
                         every_lens_factors_through_idLens
  HV4 — Lattice (lower-bound only): prodLens, IndexedJoin
  HV5 — Composition API: Factoring, ImageMinimum, OnLens (+ eqPW)
  HV6 — Pointwise equality: Lens.eqPW + view_unique_eqPW

  HV7 = `Lens/Instances/*` (concrete Lenses) — import individually
  HV8 = `Lens/Characterisation/*` (refines-relation catalog) — same

**Axiom status**: every theorem in the API is ∅-axiom (PURE).
-/
