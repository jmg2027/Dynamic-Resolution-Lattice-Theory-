import E213.Hypervisor.Compose.Factoring
import E213.Hypervisor.Compose.ImageMinimum
import E213.Hypervisor.Compose.Morphism
import E213.Hypervisor.Compose.OnLens
import E213.Hypervisor.Compose.OnLensImage
import E213.Hypervisor.Compose.OnLensImageGeneric
import E213.Hypervisor.Compose.OnLensImageLevel2

/-! Spec-as-code entry point for `E213.Hypervisor.Compose`.

  Lens composition operators.

  ## Files

    * `Factoring`           — refines-via-factor witness
    * `Morphism`            — Lens morphism composition
    * `OnLens`              — Lens ∘ Lens construction
    * `OnLensImage`,
      `OnLensImageGeneric`,
      `OnLensImageLevel2`   — image-codomain composition variants
    * `ImageMinimum`        — minimal-image witness for composed Lens
-/
