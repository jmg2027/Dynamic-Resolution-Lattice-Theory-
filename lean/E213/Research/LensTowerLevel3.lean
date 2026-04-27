import E213.Research.LensOnLensImageLevel2

/-!
# Research.LensTowerLevel3: Lens (Lens (Lens α)) image collapse

`LensOnLensImageLevel2` 의 한 step 더 — Lens (Lens (Lens α)) 의
universalMorphism 이 α 를 통 해 factor (3-level constLens
nesting).

## 의의

Recursive Lens^n α tower 의 모든 finite level 에 서 image 가
α 의 image 의 nested-constLens-pullback.  level 별 cardinality
가 *동일* — α 의 image 와 같은 cardinality.
-/

namespace E213.Research.LensTowerLevel3

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.LensOnLensImageGeneric
open E213.Research.LensOnLensImageLevel2

/-- Level-3 composite. -/
def constComposite3 (α : Type) [d : HasDistinguishing α] :
    Raw → Lens (Lens (Lens α)) :=
  fun r => constLens (constLens (constLens (@universalMorphism α d r)))

/-- **Tower collapse at level 3**. -/
theorem lensUniversalMorphism_factors_level3
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    @universalMorphism (Lens (Lens (Lens α)))
      (lensHasDistinguishing (Lens (Lens α))
        (d := lensHasDistinguishing (Lens α)
          (d := lensHasDistinguishing α))) r =
      constComposite3 α r := by
  have step1 := lensUniversalMorphism_factors_generic (Lens (Lens α))
    (d := lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)) r
  have step2 := lensUniversalMorphism_factors_level2 α (d := d) r
  rw [step1]
  unfold constComposite constComposite3
  rw [step2]
  unfold constComposite2
  rfl

end E213.Research.LensTowerLevel3
