import E213.Research.SemanticAtom

/-!
# Research.LensOnLens: Lens 자체 가 의미 framework 의 instance

Note 53 의 thesis ("meta-hierarchy 부재 — Lens 가 framework 안
또 하나 의 instance") 의 mechanical proof.

`HasDistinguishing (Lens Bool)` 의 instance 정의 — 두 distinct
Lens (constTrueLens, constFalseLens) + pointwise xor combine.

## 의의

framework 의 self-cover 의 가장 *sharp* form:
- Lens 가 framework 의 element (Raw) 가 *아니라* output type
  의 instance.
- 같은 framework abstraction (HasDistinguishing) 위 Lens type
  자체 가 instance.
- → meta-hierarchy 부재 — Lens-on-Lens 가 *새 layer* 가 아님.

universalMorphism (Lens Bool) : Raw → Lens Bool — Raw 의 element
가 Lens 로 mapping.  의미 atom 의 self-application 의 정확 한
form.
-/

namespace E213.Research.LensOnLens

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Constant-true Lens. -/
def constTrueLens : Lens Bool := ⟨true, true, fun _ _ => true⟩

/-- Constant-false Lens. -/
def constFalseLens : Lens Bool := ⟨false, false, fun _ _ => false⟩

/-- 두 constant Lens 가 distinct. -/
theorem const_lenses_distinct : constTrueLens ≠ constFalseLens := by
  intro h
  have h_base_a : constTrueLens.base_a = constFalseLens.base_a :=
    congrArg Lens.base_a h
  exact Bool.noConfusion h_base_a

end E213.Research.LensOnLens

namespace E213.Research.LensOnLens

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Lens 의 pointwise xor combine. -/
def lensXor (L M : Lens Bool) : Lens Bool :=
  ⟨xor L.base_a M.base_a, xor L.base_b M.base_b,
   fun x y => xor (L.combine x y) (M.combine x y)⟩

theorem lensXor_comm (L M : Lens Bool) : lensXor L M = lensXor M L := by
  unfold lensXor
  -- Structural equality on Lens record.
  congr 1
  · cases L.base_a <;> cases M.base_a <;> rfl
  · cases L.base_b <;> cases M.base_b <;> rfl
  · funext x y
    cases L.combine x y <;> cases M.combine x y <;> rfl

end E213.Research.LensOnLens

namespace E213.Research.LensOnLens

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Lens-on-Lens**: Lens Bool 자체 가 HasDistinguishing instance. -/
def lensBoolHasDistinguishing : HasDistinguishing (Lens Bool) where
  a := constTrueLens
  b := constFalseLens
  distinct := const_lenses_distinct
  combine := lensXor
  combine_sym := lensXor_comm

end E213.Research.LensOnLens

namespace E213.Research.LensOnLens

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Universal morphism Raw → Lens Bool

자기 self-application 의 가장 sharp instance — Raw 의 element
가 Lens (= framework 의 표현 unit) 로 mapping. -/

/-- Universal morphism Raw → Lens Bool via lens-on-lens instance. -/
def lensUniversalMorphism : Raw → Lens Bool :=
  @universalMorphism (Lens Bool) lensBoolHasDistinguishing

theorem lensUniversalMorphism_a :
    lensUniversalMorphism Raw.a = constTrueLens :=
  @universalMorphism_a (Lens Bool) lensBoolHasDistinguishing

theorem lensUniversalMorphism_b :
    lensUniversalMorphism Raw.b = constFalseLens :=
  @universalMorphism_b (Lens Bool) lensBoolHasDistinguishing

theorem lensUniversalMorphism_slash (x y : Raw) (h : x ≠ y) :
    lensUniversalMorphism (Raw.slash x y h)
      = lensXor (lensUniversalMorphism x) (lensUniversalMorphism y) :=
  @universalMorphism_slash (Lens Bool) lensBoolHasDistinguishing x y h

end E213.Research.LensOnLens
