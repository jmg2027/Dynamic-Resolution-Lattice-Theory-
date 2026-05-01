import E213.Hypervisor.Lens.Research.Lens.OnLensImageGeneric

/-!
# Research.LensOnLensImageLevel2: 2-level Lens-on-Lens collapse

Application of `LensOnLensImageGeneric`: the universalMorphism of
`Lens (Lens α)` also factors through the image of α.

## Core

```
        Raw
       /   \   \
universal α  →  α  ─constLens─→ Lens α  ─constLens─→ Lens (Lens α)
       ↘                                              ↗
        ─────────  Lens (Lens α) universal  ──────────
```

That is, the level-2 universalMorphism also passes through α, and
the image is the 2-element subset
`{constLens (constLens d.a), constLens (constLens d.b)}`
(in the Bool case).
-/

namespace E213.Hypervisor.Lens.Research.Lens.OnLensImageLevel2

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.SemanticAtom
open E213.Hypervisor.Lens.Research.LensOnLens
open E213.Hypervisor.Lens.Research.LensOnLensImageGeneric

/-- Level-2 composite: Raw → α → Lens α → Lens (Lens α). -/
def constComposite2 (α : Type) [d : HasDistinguishing α] :
    Raw → Lens (Lens α) :=
  fun r => constLens (constLens (@universalMorphism α d r))

/-- **Tower collapse at level 2**.  The universalMorphism of
    Lens (Lens α) also factors through the image of α —
    via nested constLens. -/
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

end E213.Hypervisor.Lens.Research.Lens.OnLensImageLevel2
