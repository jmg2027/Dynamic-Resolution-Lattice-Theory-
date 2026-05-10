import E213.Lens.Lattice.IndexedJoin
import E213.Lens.Lattice.JoinEquiv
import E213.Lens.Lattice.Lattice
import E213.Lens.Lattice.Meet

/-! Spec-as-code entry point for `E213.Lens.Lattice`.

  Lens lattice structure: refines preorder gives rise to
  binary meet and indexed-product (lower-bound) operations.
  Join-via-`universalLens` was removed under the
  "design-by-funext/propext 금지" directive: it required
  Prop-codomain Lens construction whose equality is propext-tainted.

  ## Files

    * `Meet`        — binary meet (prodLens)
    * `JoinEquiv`   — slash-congruence inductive (relation, not Lens)
    * `IndexedJoin` — indexed meet (iProdLens) + greatest-lower-bound
    * `Lattice`     — Lens lattice combinator
-/
