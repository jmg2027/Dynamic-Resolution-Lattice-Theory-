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
