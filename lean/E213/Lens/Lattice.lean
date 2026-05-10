import E213.Lens.Lattice.FamilyJoin
import E213.Lens.Lattice.FamilyMeet
import E213.Lens.Lattice.IndexedJoin
import E213.Lens.Lattice.Join
import E213.Lens.Lattice.JoinEquiv
import E213.Lens.Lattice.Lattice
import E213.Lens.Lattice.Meet

/-! Spec-as-code entry point for `E213.Lens.Lattice`.

  Lens lattice structure: refines preorder gives rise to
  binary join / meet and indexed / family-level operations.

  ## Files

    * `Join`        — binary join of two Lenses
    * `Meet`        — binary meet
    * `JoinEquiv`   — join up-to-equivalence
    * `IndexedJoin` — indexed join over a family
    * `FamilyJoin`  — family-level join with witness
    * `FamilyMeet`  — family-level meet
    * `Lattice`     — Lens lattice combinator
-/
