import E213.Lens.Properties.ABRefines
import E213.Lens.Properties.CanonicalForm
import E213.Lens.Properties.ConstLensTotalKernel
import E213.Lens.Properties.EquivProperties
import E213.Lens.Properties.InjectiveClass
import E213.Lens.Properties.IsLeaf
import E213.Lens.Properties.Leaf
import E213.Lens.Properties.ParityCollapseFalse
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

  All 10 included (post-M14 deferred-cluster repair):
  `ABRefines`, `Leaf`, `ParityCollapseFalse` resolved by replacing
  `open E213.Meta` with `open E213.Lens.Instances.{Bool,Parity}`.
-/
