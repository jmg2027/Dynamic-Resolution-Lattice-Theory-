import E213.Lens.Properties.CanonicalForm
import E213.Lens.Properties.ConstLensTotalKernel
import E213.Lens.Properties.EquivProperties
import E213.Lens.Properties.InjectiveClass
import E213.Lens.Properties.IsLeaf
import E213.Lens.Properties.ProdBelowId
import E213.Lens.Properties.TowerLevel3

/-! Spec-as-code entry point for `E213.Lens.Properties`.

  Derived predicates over Lenses.

  ## Files

    * `CanonicalForm`         — canonical-form normalisation
    * `EquivProperties`       — Lens equivalence preserves predicates
    * `InjectiveClass`        — injective-Lens class witness
    * `IsLeaf`                — IsLeaf predicate (no proper refinements)
    * `TowerLevel3`           — tower depth ≥ 3 witness
    * `ProdBelowId`           — Prod-Lens ⊏ id-Lens chain
    * `ConstLensTotalKernel`  — const-Lens has total kernel

  ## Status

  7/10 included.  Three deferred (pre-existing API drift):
  `ABRefines`, `Leaf`, `ParityCollapseFalse`.  See
  `research-notes/HIERARCHICAL_PLACEMENT.md` §6.1.
-/
