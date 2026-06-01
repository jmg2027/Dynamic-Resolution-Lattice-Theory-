import E213.Lens.Compose.OnLensImageGeneric

/-!
# LensOnLensImageLevel2: 2-level Lens-on-Lens collapse

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

namespace E213.Lens.Compose.OnLensImageLevel2

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Compose.OnLens
open E213.Lens.Compose.OnLensImageGeneric

/-- Level-2 composite: Raw → α → Lens α → Lens (Lens α). -/
def constComposite2 (α : Type) [d : HasDistinguishing α] :
    Raw → Lens (Lens α) :=
  fun r => constLens (constLens (@universalMorphism α d r))

/-- **Tower collapse at level 2**.  The universalMorphism of
    Lens (Lens α) also factors through the image of α — via nested constLens,
    up to the level-2 reading-sameness (`sameLens (sameLens d.same)`).  ∅-axiom:
    `sameLens`-transitivity of the level-1 factorization with its constLens
    lift (each `sameLens` component is the level-1 `step2`). -/
theorem lensUniversalMorphism_factors_level2
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    (lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)).same
      (@universalMorphism (Lens (Lens α))
        (lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)) r)
      (constComposite2 α r) := by
  have step1 := lensUniversalMorphism_factors_generic (Lens α)
    (d := lensHasDistinguishing α) r
  have step2 := lensUniversalMorphism_factors_generic α (d := d) r
  exact (lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)).same_trans step1
    ⟨step2, step2, fun _ _ => step2⟩

end E213.Lens.Compose.OnLensImageLevel2
