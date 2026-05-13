import E213.Lens.Lattice.FamilyJoin
import E213.Lens.Lattice.FamilyMeet
import E213.Lens.Lattice.IndexedJoin
import E213.Lens.Lattice.Join
import E213.Lens.Lattice.JoinEquiv
import E213.Lens.Lattice.Lattice
import E213.Lens.Lattice.Meet
import E213.Lens.Lattice.Chain
import E213.Lens.Lattice.Preorder

/-! Spec-as-code entry point for `E213.Lens.Lattice`.

  Lens lattice + refines preorder.  Refines (preorder) is the
  underlying order; Lattice (join / meet) is the algebra on top.
  Consolidated 2026-05-13 Session H from `Lens/Refines/` (preorder
  is structurally a Lattice prerequisite — folded for clarity).

  ## Refines (preorder)

    * `Chain`      — refines-chain witnesses
    * `Preorder`   — reflexivity, transitivity, antisymm-failure
                     properties of `Lens.refines`

  ## Lattice (join / meet)

    * `Join`        — binary join of two Lenses
    * `Meet`        — binary meet
    * `JoinEquiv`   — join up-to-equivalence
    * `IndexedJoin` — indexed join over a family
    * `FamilyJoin`  — family-level join with witness
    * `FamilyMeet`  — family-level meet
    * `Lattice`     — Lens lattice combinator
-/
