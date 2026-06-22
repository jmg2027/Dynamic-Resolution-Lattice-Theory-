import E213.Lens.Compose.OnLensImageLevel2

/-!
# LensTowerLevel3: Lens (Lens (Lens α)) image collapse

One step beyond `LensOnLensImageLevel2` — the universalMorphism of
Lens (Lens (Lens α)) factors through α (3-level constLens nesting).

## Significance

At every finite level of the recursive Lens^n α tower the image is
the nested-constLens pullback of the image of α.  The cardinality at
each level is *identical* — the same as the cardinality of the image
of α.
-/

namespace E213.Lens.Properties.TowerLevel3

open E213.Theory E213.Lens
open E213.Lens.Foundations.SemanticAtom
open E213.Lens.Compose.OnLens
open E213.Lens.Compose.OnLensImageGeneric
open E213.Lens.Compose.OnLensImageLevel2

/-- Level-3 composite. -/
def constComposite3 (α : Type) [d : HasDistinguishing α] :
    Raw → Lens (Lens (Lens α)) :=
  fun r => constLens (constLens (constLens (@universalMorphism α d r)))

/-- **Tower collapse at level 3** — up to the level-3 reading-sameness.
    ∅-axiom: `sameLens`-transitivity of the level-1 factorization (at
    `Lens (Lens α)`) with its constLens lift of the level-2 result. -/
theorem lensUniversalMorphism_factors_level3
    (α : Type) [d : HasDistinguishing α] (r : Raw) :
    (lensHasDistinguishing (Lens (Lens α))
        (d := lensHasDistinguishing (Lens α)
          (d := lensHasDistinguishing α))).same
      (@universalMorphism (Lens (Lens (Lens α)))
        (lensHasDistinguishing (Lens (Lens α))
          (d := lensHasDistinguishing (Lens α)
            (d := lensHasDistinguishing α))) r)
      (constComposite3 α r) := by
  have step1 := lensUniversalMorphism_factors_generic (Lens (Lens α))
    (d := lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α)) r
  have step2 := lensUniversalMorphism_factors_level2 α (d := d) r
  exact (lensHasDistinguishing (Lens (Lens α))
      (d := lensHasDistinguishing (Lens α) (d := lensHasDistinguishing α))).same_trans
    step1 ⟨step2, step2, fun _ _ => step2⟩

end E213.Lens.Properties.TowerLevel3
