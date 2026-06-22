import E213.Lens.Compose.OnLens
import E213.Lens.Properties.Morphism.BoolProp
import E213.Lens.EqPW

/-!
# LensOnLensImage: tower collapse of Lens-on-Lens

Exact characterization of the image of
`lensUniversalMorphism : Raw → Lens Bool`.

## Key Result

Image = {constTrueLens, constFalseLens} (2-element set).
The diagram commutes —

```
        Raw
       /   \
universalMorphism Bool       lensUniversalMorphism
       ↓                       ↓
      Bool ─── boolToConstLens ───→ Lens Bool
```

That is, `lensUniversalMorphism = boolToConstLens ∘ universalMorphism
Bool [boolXorHasDistinguishing]`.  The recursive structure of
Lens-on-Lens collapses at the image level to the a-leaf parity.
-/

namespace E213.Lens.Compose.OnLensImage

open E213.Theory E213.Lens
open E213.Lens.Foundations.SemanticAtom
open E213.Lens.Compose.OnLens
open E213.Lens.Properties.Morphism.BoolProp

/-- Bool → Lens Bool: second leg of the factorization. -/
def boolToConstLens (b : Bool) : Lens Bool :=
  if b then constTrueLens else constFalseLens

theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
theorem boolToConstLens_false : boolToConstLens false = constFalseLens := rfl


/-! ### lensXor acts as xor on {constTrueLens, constFalseLens} -/

theorem lensXor_TT : lensXor constTrueLens constTrueLens = constFalseLens := by
  unfold lensXor constTrueLens constFalseLens; rfl

theorem lensXor_TF : lensXor constTrueLens constFalseLens = constTrueLens := by
  unfold lensXor constTrueLens; rfl

theorem lensXor_FT : lensXor constFalseLens constTrueLens = constTrueLens := by
  unfold lensXor constTrueLens constFalseLens; rfl

theorem lensXor_FF : lensXor constFalseLens constFalseLens = constFalseLens := by
  unfold lensXor constFalseLens; rfl


/-- boolToConstLens preserves the xor combine. -/
theorem boolToConstLens_xor (x y : Bool) :
    boolToConstLens (xor x y) =
      lensXor (boolToConstLens x) (boolToConstLens y) := by
  cases x with
  | true => cases y with
    | true =>
        -- xor true true = false; lensXor constTrueLens constTrueLens = constFalseLens
        show constFalseLens = lensXor constTrueLens constTrueLens
        exact lensXor_TT.symm
    | false =>
        -- xor true false = true; lensXor constTrueLens constFalseLens = constTrueLens
        show constTrueLens = lensXor constTrueLens constFalseLens
        exact lensXor_TF.symm
  | false => cases y with
    | true =>
        show constTrueLens = lensXor constFalseLens constTrueLens
        exact lensXor_FT.symm
    | false =>
        show constFalseLens = lensXor constFalseLens constFalseLens
        exact lensXor_FF.symm


/-! ### Main: tower collapse factorization -/

/-- The composite satisfies the (a, b, slash) obligations of
    lensUniversalMorphism — assumption of universalMorphism_unique. -/
def composite (r : Raw) : Lens Bool :=
  boolToConstLens (@universalMorphism Bool boolXorHasDistinguishing r)

theorem composite_a : composite Raw.a = constTrueLens := by
  unfold composite
  rw [@universalMorphism_a Bool boolXorHasDistinguishing]
  rfl

theorem composite_b : composite Raw.b = constFalseLens := by
  unfold composite
  rw [@universalMorphism_b Bool boolXorHasDistinguishing]
  rfl

theorem composite_slash (x y : Raw) (h : x ≠ y) :
    composite (Raw.slash x y h) = lensXor (composite x) (composite y) := by
  unfold composite
  -- `universalMorphism_slash` is stated up to `same`; at the `Bool` codomain
  -- `same = Eq`, extracted here (default-transparency ascription) for the `rw`.
  have e : @universalMorphism Bool boolXorHasDistinguishing (Raw.slash x y h)
         = boolXorHasDistinguishing.combine
             (@universalMorphism Bool boolXorHasDistinguishing x)
             (@universalMorphism Bool boolXorHasDistinguishing y) :=
    @universalMorphism_slash Bool boolXorHasDistinguishing x y h
  rw [e]
  exact boolToConstLens_xor _ _

/-- ∅-axiom (the residue-native tower collapse): pointwise
    Lens equality (eqPW) of `lensUniversalMorphism r` and `composite r`,
    avoiding funext on the combine field via `Lens.view_unique_eqPW`. -/
theorem lensUniversalMorphism_factors_eqPW (r : Raw) :
    (lensUniversalMorphism r).eqPW (composite r) := by
  have h := Lens.view_unique_eqPW
    (β := Bool)
    (L := ⟨constTrueLens, constFalseLens, lensXor⟩)
    (fun u v => lensXor_comm_eqPW u v)
    (fun u u' v v' hu hv => lensXor_eqPW_cong u u' v v' hu hv)
    composite
    (by show (composite Raw.a).eqPW constTrueLens
        rw [composite_a]; exact Lens.eqPW_refl _)
    (by show (composite Raw.b).eqPW constFalseLens
        rw [composite_b]; exact Lens.eqPW_refl _)
    (by intro x y h
        show (composite (Raw.slash x y h)).eqPW
              (lensXor (composite x) (composite y))
        rw [composite_slash x y h]; exact Lens.eqPW_refl _)
    r
  -- h : (composite r).eqPW (⟨...⟩.view r) = (composite r).eqPW (lensUniversalMorphism r)
  exact Lens.eqPW_symm h


/-- ∅-axiom: pointwise (eqPW) image characterization — the image of
    lensUniversalMorphism is exactly {constTrueLens, constFalseLens}. -/
theorem lensUniversalMorphism_image_eqPW (r : Raw) :
    (lensUniversalMorphism r).eqPW constTrueLens ∨
    (lensUniversalMorphism r).eqPW constFalseLens := by
  have hf := lensUniversalMorphism_factors_eqPW r
  -- composite r = boolToConstLens (universalMorphism Bool ... r)
  -- boolToConstLens true = constTrueLens, boolToConstLens false = constFalseLens
  cases hum : @universalMorphism Bool boolXorHasDistinguishing r
  · right
    have : composite r = constFalseLens := by
      unfold composite; rw [hum]; rfl
    exact this ▸ hf
  · left
    have : composite r = constTrueLens := by
      unfold composite; rw [hum]; rfl
    exact this ▸ hf

end E213.Lens.Compose.OnLensImage
