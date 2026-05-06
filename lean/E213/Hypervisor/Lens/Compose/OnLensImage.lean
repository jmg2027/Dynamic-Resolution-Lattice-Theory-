import E213.Hypervisor.Lens.Compose.OnLens
import E213.Hypervisor.Lens.Morphism.BoolProp

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

namespace E213.Hypervisor.Lens.Compose.OnLensImage

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.Compose.OnLens
open E213.Hypervisor.Lens.Morphism.BoolProp

/-- Bool → Lens Bool: second leg of the factorization. -/
def boolToConstLens (b : Bool) : Lens Bool :=
  if b then constTrueLens else constFalseLens

theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
theorem boolToConstLens_false : boolToConstLens false = constFalseLens := rfl

end E213.Hypervisor.Lens.Compose.OnLensImage

namespace E213.Hypervisor.Lens.Compose.OnLensImage

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.Compose.OnLens
open E213.Hypervisor.Lens.Morphism.BoolProp

/-! ### lensXor acts as xor on {constTrueLens, constFalseLens} -/

theorem lensXor_TT : lensXor constTrueLens constTrueLens = constFalseLens := by
  unfold lensXor constTrueLens constFalseLens; rfl

theorem lensXor_TF : lensXor constTrueLens constFalseLens = constTrueLens := by
  unfold lensXor constTrueLens; rfl

theorem lensXor_FT : lensXor constFalseLens constTrueLens = constTrueLens := by
  unfold lensXor constTrueLens constFalseLens; rfl

theorem lensXor_FF : lensXor constFalseLens constFalseLens = constFalseLens := by
  unfold lensXor constFalseLens; rfl

end E213.Hypervisor.Lens.Compose.OnLensImage

namespace E213.Hypervisor.Lens.Compose.OnLensImage

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.Compose.OnLens
open E213.Hypervisor.Lens.Morphism.BoolProp

/-- boolToConstLens preserves the xor combine. -/
theorem boolToConstLens_xor (x y : Bool) :
    boolToConstLens (xor x y) =
      lensXor (boolToConstLens x) (boolToConstLens y) := by
  cases x <;> cases y <;>
    simp [boolToConstLens, lensXor_TT, lensXor_TF, lensXor_FT, lensXor_FF]

end E213.Hypervisor.Lens.Compose.OnLensImage

namespace E213.Hypervisor.Lens.Compose.OnLensImage

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.Compose.OnLens
open E213.Hypervisor.Lens.Morphism.BoolProp

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
  rw [@universalMorphism_slash Bool boolXorHasDistinguishing x y h]
  exact boolToConstLens_xor _ _

end E213.Hypervisor.Lens.Compose.OnLensImage

namespace E213.Hypervisor.Lens.Compose.OnLensImage

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.Compose.OnLens
open E213.Hypervisor.Lens.Morphism.BoolProp

/-- **Tower collapse**: lensUniversalMorphism factors through
    universalMorphism Bool.  The image of Lens-on-Lens equals the
    image of boolToConstLens = {constTrueLens, constFalseLens}. -/
theorem lensUniversalMorphism_factors (r : Raw) :
    lensUniversalMorphism r = composite r := by
  have h := @universalMorphism_unique (Lens Bool) lensBoolHasDistinguishing
    composite composite_a composite_b composite_slash r
  exact h.symm

end E213.Hypervisor.Lens.Compose.OnLensImage

namespace E213.Hypervisor.Lens.Compose.OnLensImage

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.Compose.OnLens
open E213.Hypervisor.Lens.Morphism.BoolProp

/-- **Image characterization**: the image of lensUniversalMorphism is
    exactly 2 elements — {constTrueLens, constFalseLens}. -/
theorem lensUniversalMorphism_image (r : Raw) :
    lensUniversalMorphism r = constTrueLens ∨
    lensUniversalMorphism r = constFalseLens := by
  rw [lensUniversalMorphism_factors]
  unfold composite boolToConstLens
  cases @universalMorphism Bool boolXorHasDistinguishing r
  · right; rfl
  · left; rfl

end E213.Hypervisor.Lens.Compose.OnLensImage
