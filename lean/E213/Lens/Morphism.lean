import E213.Lens.Morphism.BoolProp
import E213.Lens.Morphism.BoolSqClassification
import E213.Lens.Morphism.DepthParityNotFold
import E213.Lens.Morphism.Dist
import E213.Lens.Morphism.FoldStructured
import E213.Lens.Morphism.NoDepthParity
import E213.Lens.Morphism.SlashCharNotFold
import E213.Lens.Morphism.SlashSwap

/-! Spec-as-code entry point for `E213.Lens.Morphism`.

  Lens-morphism shape catalogue: which Raw → α functions are
  expressible as a Lens view, and which are not.

  ## Files

    * `FoldStructured`     — fold-structured-view characterisation
    * `BoolProp`           — Bool-valued Prop witness
    * `Dist`               — distributivity / commutation lemmas
    * `SlashSwap`          — slash + swap interaction
    * `NoDepthParity`,
      `DepthParityNotFold` — depth+parity is NOT fold-structured
                              (negative-side characterisation)

  ## Status

  All 8 included (post-M14 deferred-cluster repair).
  `BoolSqClassification` re-routed through `E213.Lens.Diagonal`;
  `SlashCharNotFold` resolved by namespace-drift repair.
-/
