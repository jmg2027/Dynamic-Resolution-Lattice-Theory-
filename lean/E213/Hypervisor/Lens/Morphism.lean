import E213.Hypervisor.Lens.Morphism.BoolProp
import E213.Hypervisor.Lens.Morphism.DepthParityNotFold
import E213.Hypervisor.Lens.Morphism.Dist
import E213.Hypervisor.Lens.Morphism.FoldStructured
import E213.Hypervisor.Lens.Morphism.NoDepthParity
import E213.Hypervisor.Lens.Morphism.SlashSwap

/-! Spec-as-code entry point for `E213.Hypervisor.Lens.Morphism`.

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
