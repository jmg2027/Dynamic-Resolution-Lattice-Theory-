import E213.Lens.Compose.Factoring
import E213.Lens.Compose.ImageMinimum
import E213.Lens.Compose.Morphism
import E213.Lens.Compose.OnLens
import E213.Lens.Compose.OnLensImage
import E213.Lens.Compose.OnLensImageGeneric
import E213.Lens.Compose.OnLensImageLevel2

/-! Spec-as-code entry point for `E213.Lens.Compose`.

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
