import E213.Lens.Properties.ABRefines
import E213.Lens.Properties.CanonicalForm
import E213.Lens.Properties.ConstLensTotalKernel
import E213.Lens.Properties.Diagonal
import E213.Lens.Properties.EquivProperties
import E213.Lens.Properties.InjectiveClass
import E213.Lens.Properties.IsLeaf
import E213.Lens.Properties.Leaf
import E213.Lens.Properties.ParityCollapseFalse
import E213.Lens.Properties.ProdBelowId
import E213.Lens.Properties.TowerLevel3
import E213.Lens.Properties.Characterisation.Catalog
import E213.Lens.Properties.Characterisation.Core
import E213.Lens.Properties.Morphism.BoolProp
import E213.Lens.Properties.Morphism.BoolSqClassification
import E213.Lens.Properties.Morphism.DepthParityNotFold
import E213.Lens.Properties.Morphism.Dist
import E213.Lens.Properties.Morphism.FoldStructured
import E213.Lens.Properties.Morphism.NoDepthParity
import E213.Lens.Properties.Morphism.SlashCharNotFold
import E213.Lens.Properties.Morphism.SlashSwap

/-! Spec-as-code entry point for `E213.Lens.Properties`.

  Derived predicates over Lenses + characterisation + morphism shape
  + diagonal classification. Session H by
  absorbing `Characterisation/`, `Morphism/`, and root `Diagonal.lean`
  per LENS_AUDIT §4 — all are "properties of lenses" semantically.

  ## Flat predicates (10)

    * `CanonicalForm`         — canonical-form normalisation
    * `EquivProperties`       — Lens equivalence preserves predicates
    * `InjectiveClass`        — injective-Lens class witness
    * `IsLeaf`                — IsLeaf predicate (no proper refinements)
    * `Leaf`                  — Leaf-related predicates
    * `TowerLevel3`           — tower depth ≥ 3 witness
    * `ProdBelowId`           — Prod-Lens ⊏ id-Lens chain
    * `ConstLensTotalKernel`  — const-Lens has total kernel
    * `ABRefines`             — AB-Lens refines-relation
    * `ParityCollapseFalse`   — parity-collapse negation

  ## Diagonal (sq L classification, 1 file)

    * `Diagonal`              — Collapse / Idempotent / Escalate /
                                Multiply over Bool, Nat, F9

  ## Characterisation/ (2 files — binary-combine ↔ Lens combine)

    * `Characterisation/Core`    — characterisation typeclasses
    * `Characterisation/Catalog` — catalogue of binary-combine
                                    instances

  ## Morphism/ (8 files — which Raw → α expressible as Lens view)

    * `Morphism/FoldStructured`     — fold-structured-view char.
    * `Morphism/BoolProp`           — Bool-valued Prop witness
    * `Morphism/Dist`               — distributivity / commutation
    * `Morphism/SlashSwap`          — slash + swap interaction
    * `Morphism/NoDepthParity`,
      `Morphism/DepthParityNotFold` — depth+parity NOT fold-structured
    * `Morphism/SlashCharNotFold`   — slash-char NOT fold-structured
    * `Morphism/BoolSqClassification` — Bool-sq classification
                                          (uses `Diagonal`)
-/
