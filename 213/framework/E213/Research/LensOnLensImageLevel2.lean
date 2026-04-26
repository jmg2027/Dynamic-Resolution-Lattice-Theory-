import E213.Research.LensOnLensImageGeneric

/-!
# Research.LensOnLensImageLevel2: 2-level Lens-on-Lens collapse

`LensOnLensImageGeneric` 의 응용: `Lens (Lens α)` 의
universalMorphism 도 α 의 image 를 통 해 factor.

## 핵심

```
        Raw
       /   \   \
universal α  →  α  ─constLens─→ Lens α  ─constLens─→ Lens (Lens α)
       ↘                                              ↗
        ─────────  Lens (Lens α) universal  ──────────
```

즉 level-2 의 universalMorphism 도 α 를 거치며, image 가
`{constLens (constLens d.a), constLens (constLens d.b)}` 의
2-element subset (Bool case 의 경우).
-/

namespace E213.Research.LensOnLensImageLevel2

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.LensOnLensImageGeneric

/-- Level-2 composite: Raw → α → Lens α → Lens (Lens α). -/
def constComposite2 (α : Type) [d : HasDistinguishing α] :
    Raw → Lens (Lens α) :=
  fun r => constLens (constLens (@universalMorphism α d r))

/-- **Tower collapse at level 2**.  Lens (Lens α) 의
    universalMorphism 도 α 의 image 를 통 해 factor —
    nested constLens 으 로. -/
theorem lensUniversalMorphism_factors_level2
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    @universalMorphism (Lens (Lens α))
      (lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)) r =
      constComposite2 α r := by
  have step1 := lensUniversalMorphism_factors_generic (Lens α)
    (d := lensHasDistinguishing α) r
  -- step1: universalMorphism (Lens (Lens α)) r = constLens (universalMorphism (Lens α) r)
  have step2 := lensUniversalMorphism_factors_generic α (d := d) r
  -- step2: universalMorphism (Lens α) r = constLens (universalMorphism α r)
  rw [step1]
  unfold constComposite constComposite2
  rw [step2]
  rfl

end E213.Research.LensOnLensImageLevel2
