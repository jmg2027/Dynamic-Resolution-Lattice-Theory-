import E213.Hypervisor.SemanticAtom
import E213.Hypervisor.Compose.OnLens
import E213.Hypervisor.Compose.OnLensImageGeneric

/-!
# UniversalMorphismFactor: image-Lens of universalMorphism
Functional form

Application of the reflection theorem `UniversalReflection` from PAPER1 §9.2:
universalMorphism can always be expressed as the view of some Lens.

## Core

`universal_morphism_view`: `universalMorphism α r =
(universalAsLens α).view r` for any HasDistinguishing α.

Direct consequence of the universalAsLens definition in `UniversalReflection.lean`.
-/

namespace E213.Meta.Universal.MorphismFactor

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.SemanticAtom
open E213.Hypervisor.Compose.OnLens
open E213.Hypervisor.Compose.OnLensImageGeneric

/-- universalMorphism agrees with the view of universalAsLens (by
    definition of `universalAsLens`). -/
theorem constComposite_a_unfold (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.a = constLens d.a := constComposite_a α

theorem constComposite_b_unfold (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.b = constLens d.b := constComposite_b α

end E213.Meta.Universal.MorphismFactor
