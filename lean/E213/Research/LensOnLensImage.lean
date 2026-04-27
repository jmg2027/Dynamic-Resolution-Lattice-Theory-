import E213.Research.LensOnLens
import E213.Research.BoolPropMorphism

/-!
# Research.LensOnLensImage: Lens-on-Lens 의 tower collapse

`lensUniversalMorphism : Raw → Lens Bool` 의 image 의 정확 한
characterization.

## 핵심 결과

Image = {constTrueLens, constFalseLens} (2-element set).
Diagram commutes —

```
        Raw
       /   \
universalMorphism Bool       lensUniversalMorphism
       ↓                       ↓
      Bool ─── boolToConstLens ───→ Lens Bool
```

즉 `lensUniversalMorphism = boolToConstLens ∘ universalMorphism
Bool [boolXorHasDistinguishing]`.  Lens-on-Lens 의 recursive
structure 가 image level 에서 a-leaf parity 로 collapse.
-/

namespace E213.Research.LensOnLensImage

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.BoolPropMorphism

/-- Bool → Lens Bool: factorization 의 second leg. -/
def boolToConstLens (b : Bool) : Lens Bool :=
  if b then constTrueLens else constFalseLens

theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
theorem boolToConstLens_false : boolToConstLens false = constFalseLens := rfl

end E213.Research.LensOnLensImage

namespace E213.Research.LensOnLensImage

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.BoolPropMorphism

/-! ### lensXor 가 {constTrueLens, constFalseLens} 위 에서 xor -/

theorem lensXor_TT : lensXor constTrueLens constTrueLens = constFalseLens := by
  unfold lensXor constTrueLens constFalseLens; rfl

theorem lensXor_TF : lensXor constTrueLens constFalseLens = constTrueLens := by
  unfold lensXor constTrueLens; rfl

theorem lensXor_FT : lensXor constFalseLens constTrueLens = constTrueLens := by
  unfold lensXor constTrueLens constFalseLens; rfl

theorem lensXor_FF : lensXor constFalseLens constFalseLens = constFalseLens := by
  unfold lensXor constFalseLens; rfl

end E213.Research.LensOnLensImage

namespace E213.Research.LensOnLensImage

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.BoolPropMorphism

/-- boolToConstLens 가 xor combine 보존. -/
theorem boolToConstLens_xor (x y : Bool) :
    boolToConstLens (xor x y) =
      lensXor (boolToConstLens x) (boolToConstLens y) := by
  cases x <;> cases y <;>
    simp [boolToConstLens, lensXor_TT, lensXor_TF, lensXor_FT, lensXor_FF]

end E213.Research.LensOnLensImage

namespace E213.Research.LensOnLensImage

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.BoolPropMorphism

/-! ### Main: tower collapse factorization -/

/-- Composite 가 lensUniversalMorphism 의 (a, b, slash) 의무
    를 만족 — universalMorphism_unique 의 가정. -/
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

end E213.Research.LensOnLensImage

namespace E213.Research.LensOnLensImage

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.BoolPropMorphism

/-- **Tower collapse**: lensUniversalMorphism 가 universalMorphism Bool
    을 통해 factor.  Lens-on-Lens 의 image 가 boolToConstLens 의
    image = {constTrueLens, constFalseLens}. -/
theorem lensUniversalMorphism_factors (r : Raw) :
    lensUniversalMorphism r = composite r := by
  have h := @universalMorphism_unique (Lens Bool) lensBoolHasDistinguishing
    composite composite_a composite_b composite_slash r
  exact h.symm

end E213.Research.LensOnLensImage

namespace E213.Research.LensOnLensImage

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.LensOnLens
open E213.Research.BoolPropMorphism

/-- **Image characterization**: lensUniversalMorphism 의 image
    가 정확 히 2 elements — {constTrueLens, constFalseLens}. -/
theorem lensUniversalMorphism_image (r : Raw) :
    lensUniversalMorphism r = constTrueLens ∨
    lensUniversalMorphism r = constFalseLens := by
  rw [lensUniversalMorphism_factors]
  unfold composite boolToConstLens
  cases @universalMorphism Bool boolXorHasDistinguishing r
  · right; rfl
  · left; rfl

end E213.Research.LensOnLensImage
