import E213.Lens.API
import E213.Lens.LensCore
import E213.Lens.AxiomLenses.Core
import E213.Lens.Characterisation
import E213.Lens.Compose
import E213.Lens.Diagonal
import E213.Lens.Initiality
import E213.Lens.Instances
import E213.Lens.Algebra
import E213.Lens.Lattice
import E213.Lens.Leaves
import E213.Lens.Morphism
import E213.Lens.Properties
import E213.Lens.Refines
import E213.Lens.SemanticAtom
import E213.Lens.EqPW

/-! Spec-as-code entry point for `E213.Lens`.

  Lens layer — the Lens algebra.

  Removed (design-by-funext/propext 금지):
    * `Lens.Universal` umbrella — `universalLens (Raw → Prop)`
      construction was propext-by-design; replaced with `Lens.EqPW`
      (pointwise equality, ∅-axiom).

  ## Chapters

    * `AxiomLenses` — axiom-lens family
    * `Characterisation` — Catalog + Core
    * `Compose` — composition operators (Factoring, OnLens, ImageMinimum,
                    Morphism, OnLensImage / OnLensImageGeneric eqPW chains)
    * `Diagonal` — diagonal (sq) classification
    * `Instances` — concrete Lens instances
    * `Algebra` — equational layer (Congruence, IdLensEq, etc.)
    * `Lattice` — Meet + IndexedJoin (lower-bound)
    * `Leaves` — depth-leaf hierarchy
    * `Morphism` — morphism shape catalogue
    * `Properties` — derived predicates
    * `Refines` — refines preorder
    * `EqPW` — pointwise Lens equality (avoids funext-by-design)

  ## Top-level

    * `API.lean` — public surface
    * `LensCore.lean` — Lens type + view/equiv
    * `Initiality.lean` — initiality
    * `SemanticAtom.lean` — semantic-atom characterisation
-/
