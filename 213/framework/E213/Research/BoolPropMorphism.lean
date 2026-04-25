import E213.Research.SemanticAtom
import E213.Research.InstanceReach

/-!
# Research.BoolPropMorphism: Bool → Prop morphism

`Bool` 과 `Prop` 모두 의미 framework 의 instance.  이 둘 사이
의 *structure-preserving morphism* 의 직접 형식.

`DistMorphism` 의 typeclass-based 형식 이 multiple Prop instance
의 synthesis 부재 — explicit record 로 직접 형식.
-/

namespace E213.Research.BoolPropMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-- Bool → Prop, b ↦ (b = true).  Bool.and ↔ Prop.And 의 structure
    preservation. -/
def boolToProp (b : Bool) : Prop := b = true

theorem boolToProp_true : boolToProp true = True := by
  unfold boolToProp
  apply propext
  exact ⟨fun _ => trivial, fun _ => rfl⟩

theorem boolToProp_false : boolToProp false = False := by
  unfold boolToProp
  apply propext
  exact ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩

theorem boolToProp_and (x y : Bool) :
    boolToProp (Bool.and x y) = (boolToProp x ∧ boolToProp y) := by
  unfold boolToProp
  cases x <;> cases y <;> simp

end E213.Research.BoolPropMorphism

namespace E213.Research.BoolPropMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-- **Functorial commutativity**: Raw 의 universal morphism Bool 과
    Prop (And) 의 image 가 boolToProp 으로 commute.

    universalMorphism Prop = boolToProp ∘ universalMorphism Bool. -/
theorem universalMorphism_commute (r : Raw) :
    @universalMorphism Prop propAsDistinguishingAnd r
      = boolToProp (universalMorphism Bool r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingAnd Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingAnd
      have h2 : universalMorphism Bool Raw.a = true :=
        universalMorphism_a Bool
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishingAnd Raw.b = False :=
        @universalMorphism_b Prop propAsDistinguishingAnd
      have h2 : universalMorphism Bool Raw.b = false :=
        universalMorphism_b Bool
      rw [h1, h2, boolToProp_false]
  | slash x y h ihx ihy =>
      have h1 : @universalMorphism Prop propAsDistinguishingAnd
                  (Raw.slash x y h)
                = (@universalMorphism Prop propAsDistinguishingAnd x ∧
                   @universalMorphism Prop propAsDistinguishingAnd y) :=
        @universalMorphism_slash Prop propAsDistinguishingAnd x y h
      have h2 : universalMorphism Bool (Raw.slash x y h)
                = Bool.and (universalMorphism Bool x) (universalMorphism Bool y) :=
        universalMorphism_slash Bool x y h
      rw [h1, h2, boolToProp_and, ihx, ihy]

end E213.Research.BoolPropMorphism

namespace E213.Research.BoolPropMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-! ### Bool with Xor + Prop with Xor 의 commute

이전 (위 의) Bool (and) ↔ Prop (And) 외 의 다른 connective pair
의 functoriality.

Bool 의 xor instance + Prop 의 propXor instance.  같은 boolToProp
morphism 으로 commute. -/

/-- Bool with xor combine instance. -/
def boolXorHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := xor
  combine_sym := by intros x y; cases x <;> cases y <;> rfl

/-- boolToProp 가 xor combine 보존 (Bool xor → Prop propXor). -/
theorem boolToProp_xor (x y : Bool) :
    boolToProp (xor x y) = propXor (boolToProp x) (boolToProp y) := by
  unfold boolToProp propXor
  cases x <;> cases y <;> simp [xor]

/-- **Functorial commutativity (Xor pair)**: Bool (xor) instance 의
    universalMorphism 이 Prop (Xor) 의 universalMorphism 으로 commute
    via boolToProp. -/
theorem universalMorphism_commute_xor (r : Raw) :
    @universalMorphism Prop propAsDistinguishing r
      = boolToProp (@universalMorphism Bool boolXorHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishing Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishing
      have h2 : @universalMorphism Bool boolXorHasDistinguishing Raw.a = true :=
        @universalMorphism_a Bool boolXorHasDistinguishing
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishing Raw.b = False :=
        @universalMorphism_b Prop propAsDistinguishing
      have h2 : @universalMorphism Bool boolXorHasDistinguishing Raw.b = false :=
        @universalMorphism_b Bool boolXorHasDistinguishing
      rw [h1, h2, boolToProp_false]
  | slash x y h ihx ihy =>
      have h1 : @universalMorphism Prop propAsDistinguishing (Raw.slash x y h)
                = propXor
                    (@universalMorphism Prop propAsDistinguishing x)
                    (@universalMorphism Prop propAsDistinguishing y) :=
        @universalMorphism_slash Prop propAsDistinguishing x y h
      have h2 : @universalMorphism Bool boolXorHasDistinguishing (Raw.slash x y h)
                = xor (@universalMorphism Bool boolXorHasDistinguishing x)
                      (@universalMorphism Bool boolXorHasDistinguishing y) :=
        @universalMorphism_slash Bool boolXorHasDistinguishing x y h
      rw [h1, h2, boolToProp_xor, ihx, ihy]

end E213.Research.BoolPropMorphism

namespace E213.Research.BoolPropMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-! ### Or, Iff connective pairs 의 functoriality -/

/-- Bool with or combine instance. -/
def boolOrHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := Bool.or
  combine_sym := Bool.or_comm

/-- boolToProp 가 or combine 보존. -/
theorem boolToProp_or (x y : Bool) :
    boolToProp (Bool.or x y) = (boolToProp x ∨ boolToProp y) := by
  unfold boolToProp
  cases x <;> cases y <;> simp

/-- **Functorial commutativity (Or pair)**. -/
theorem universalMorphism_commute_or (r : Raw) :
    @universalMorphism Prop propAsDistinguishingOr r
      = boolToProp (@universalMorphism Bool boolOrHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingOr Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingOr
      have h2 : @universalMorphism Bool boolOrHasDistinguishing Raw.a = true :=
        @universalMorphism_a Bool boolOrHasDistinguishing
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishingOr Raw.b = False :=
        @universalMorphism_b Prop propAsDistinguishingOr
      have h2 : @universalMorphism Bool boolOrHasDistinguishing Raw.b = false :=
        @universalMorphism_b Bool boolOrHasDistinguishing
      rw [h1, h2, boolToProp_false]
  | slash x y h ihx ihy =>
      have h1 : @universalMorphism Prop propAsDistinguishingOr (Raw.slash x y h)
                = ((@universalMorphism Prop propAsDistinguishingOr x) ∨
                   (@universalMorphism Prop propAsDistinguishingOr y)) :=
        @universalMorphism_slash Prop propAsDistinguishingOr x y h
      have h2 : @universalMorphism Bool boolOrHasDistinguishing (Raw.slash x y h)
                = Bool.or (@universalMorphism Bool boolOrHasDistinguishing x)
                          (@universalMorphism Bool boolOrHasDistinguishing y) :=
        @universalMorphism_slash Bool boolOrHasDistinguishing x y h
      rw [h1, h2, boolToProp_or, ihx, ihy]

end E213.Research.BoolPropMorphism

namespace E213.Research.BoolPropMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-- Bool with beq (= equality on Bool) combine instance. -/
def boolIffHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := fun x y => decide (x = y)
  combine_sym := by intros x y; cases x <;> cases y <;> rfl

/-- boolToProp 가 Iff combine 보존. -/
theorem boolToProp_iff (x y : Bool) :
    boolToProp (decide (x = y)) = (boolToProp x ↔ boolToProp y) := by
  unfold boolToProp
  cases x <;> cases y <;> simp

/-- **Functorial commutativity (Iff pair)**. -/
theorem universalMorphism_commute_iff (r : Raw) :
    @universalMorphism Prop propAsDistinguishingIff r
      = boolToProp (@universalMorphism Bool boolIffHasDistinguishing r) := by
  induction r using Raw.rec with
  | a =>
      have h1 : @universalMorphism Prop propAsDistinguishingIff Raw.a = True :=
        @universalMorphism_a Prop propAsDistinguishingIff
      have h2 : @universalMorphism Bool boolIffHasDistinguishing Raw.a = true :=
        @universalMorphism_a Bool boolIffHasDistinguishing
      rw [h1, h2, boolToProp_true]
  | b =>
      have h1 : @universalMorphism Prop propAsDistinguishingIff Raw.b = False :=
        @universalMorphism_b Prop propAsDistinguishingIff
      have h2 : @universalMorphism Bool boolIffHasDistinguishing Raw.b = false :=
        @universalMorphism_b Bool boolIffHasDistinguishing
      rw [h1, h2, boolToProp_false]
  | slash x y h ihx ihy =>
      have h1 : @universalMorphism Prop propAsDistinguishingIff (Raw.slash x y h)
                = ((@universalMorphism Prop propAsDistinguishingIff x) ↔
                   (@universalMorphism Prop propAsDistinguishingIff y)) :=
        @universalMorphism_slash Prop propAsDistinguishingIff x y h
      have h2 : @universalMorphism Bool boolIffHasDistinguishing (Raw.slash x y h)
                = decide
                    ((@universalMorphism Bool boolIffHasDistinguishing x)
                     = (@universalMorphism Bool boolIffHasDistinguishing y)) :=
        @universalMorphism_slash Bool boolIffHasDistinguishing x y h
      rw [h1, h2, boolToProp_iff, ihx, ihy]

end E213.Research.BoolPropMorphism
