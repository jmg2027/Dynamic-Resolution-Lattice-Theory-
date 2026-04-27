import E213.Research.SemanticAtom
import E213.Research.LensOnLens
import E213.Research.LensOnLensImageGeneric

/-!
# Research.UniversalMorphismFactor: universalMorphism 의 image-Lens
함수형 form

PAPER1 §9.2 의 reflection theorem `UniversalReflection` 의 응용:
universalMorphism 이 항상 어떤 Lens 의 view 로 표현 가능.

## 핵심

`universal_morphism_view`: `universalMorphism α r =
(universalAsLens α).view r` for any HasDistinguishing α.

`UniversalReflection.lean` 의 universalAsLens 정의 의 직접 결과.
-/

namespace E213.Research.UniversalMorphismFactor

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.LensOnLensImageGeneric

/-- universalMorphism 이 universalAsLens 의 view 와 일치 (by
    `universalAsLens` 정의). -/
theorem constComposite_a_unfold (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.a = constLens d.a := constComposite_a α

theorem constComposite_b_unfold (α : Type) [d : HasDistinguishing α] :
    constComposite α Raw.b = constLens d.b := constComposite_b α

end E213.Research.UniversalMorphismFactor
