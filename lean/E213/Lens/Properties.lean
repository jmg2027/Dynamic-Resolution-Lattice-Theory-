import E213.Lens.Properties.ConstLensTotalKernel
import E213.Lens.Properties.EquivProperties
import E213.Lens.Properties.InjectiveClass
import E213.Lens.Properties.IsLeaf
import E213.Lens.Properties.Leaf
import E213.Lens.Properties.ParityCollapseFalse
import E213.Lens.Properties.ProdBelowId

/-! Spec-as-code entry point for `E213.Lens.Properties`.

  Derived predicates over Lenses.

  Removed (design-by-funext/propext 금지):
    * `CanonicalForm`  — used `universalLens (Raw → Prop)`
    * `TowerLevel3`    — Lens-eq theorem requiring funext on combine
                          (the Lens-on-Lens tower demos; eqPW versions
                          live in `Lens/Compose/OnLens` for level 1)

  ## Files

    * `EquivProperties`       — Lens equivalence preserves predicates
    * `InjectiveClass`        — injective-Lens class witness
    * `IsLeaf`                — IsLeaf predicate (no proper refinements)
    * `ProdBelowId`           — Prod-Lens ⊏ id-Lens chain
    * `ConstLensTotalKernel`  — const-Lens has total kernel
-/
