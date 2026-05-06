import E213.Hypervisor.Lattice.FamilyJoin
import E213.Hypervisor.Lattice.FamilyMeet
import E213.Hypervisor.Lattice.IndexedJoin
import E213.Hypervisor.Lattice.Join
import E213.Hypervisor.Lattice.JoinEquiv
import E213.Hypervisor.Lattice.Lattice
import E213.Hypervisor.Lattice.Meet

/-! Spec-as-code entry point for `E213.Hypervisor.Lattice`.

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
