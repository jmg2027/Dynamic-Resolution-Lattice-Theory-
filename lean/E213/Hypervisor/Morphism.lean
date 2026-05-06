import E213.Hypervisor.Morphism.BoolProp
import E213.Hypervisor.Morphism.DepthParityNotFold
import E213.Hypervisor.Morphism.Dist
import E213.Hypervisor.Morphism.FoldStructured
import E213.Hypervisor.Morphism.NoDepthParity
import E213.Hypervisor.Morphism.SlashSwap

/-! Spec-as-code entry point for `E213.Hypervisor.Morphism`.

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

  6/8 included.  Two deferred (pre-existing API drift):
  `BoolSqClassification`, `SlashCharNotFold`.  See
  `research-notes/HIERARCHICAL_PLACEMENT.md` §6.1.
-/
