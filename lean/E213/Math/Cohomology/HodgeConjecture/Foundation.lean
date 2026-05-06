import E213.Math.Cohomology.HodgeConjecture.Foundation.Canonical
import E213.Math.Cohomology.HodgeConjecture.Foundation.Complete
import E213.Math.Cohomology.HodgeConjecture.Foundation.Conjecture
import E213.Math.Cohomology.HodgeConjecture.Foundation.ConjectureLens
import E213.Math.Cohomology.HodgeConjecture.Foundation.Filled
import E213.Math.Cohomology.HodgeConjecture.Foundation.LensCata

/-! Spec-as-code entry point for `E213.Math.Cohomology.HodgeConjecture.Foundation`.

  Foundational layer of the 213-native Hodge-conjecture programme.

  ## Files

    * `Conjecture`     — formal statement of the Hodge conjecture
                         in 213-native cochain language
    * `ConjectureLens` — Lens-formulation of the conjecture
    * `Canonical`      — canonical-form witness
    * `LensCata`       — Lens catamorphism scaffolding
    * `Filled`         — 2-cell-filled cochain extension
    * `Complete`       — completeness witness for the foundation
                         layer (everything below builds on this)
-/
