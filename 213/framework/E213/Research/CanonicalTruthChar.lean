import E213.Research.SemanticAtom

/-!
# Research.CanonicalTruthChar: canonicalTruthMap 의 정확 한 characterization

`SemanticAtom.canonicalTruthMap : Raw → Prop` (Xor-based) 의
의미: 각 Raw 의 truth value 가 무엇 으로 결정 되는가?

**결과**: `canonicalTruthMap r ↔ (a count of r) is odd`.

즉 Prop instance 의 universal morphism 이 정확히 *Raw 의 a-count
parity* 를 추출.  의미 atom 의 self-application 의 정확 한 form.

## 구성

Bool-valued analog: `aCountParityLens : Lens Bool := ⟨true, false,
xor⟩`.  view r = a-count parity (true iff odd).

그리고 canonicalTruthMap r = (aCountParityLens.view r = true)
의 Prop 변환.
-/

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Bool-valued a-count parity Lens. -/
def aCountParityLens : Lens Bool := ⟨true, false, fun x y => xor x y⟩

theorem aCountParityLens_a : aCountParityLens.view Raw.a = true := rfl
theorem aCountParityLens_b : aCountParityLens.view Raw.b = false := rfl

theorem aCountParityLens_slash (x y : Raw) (h : x ≠ y) :
    aCountParityLens.view (Raw.slash x y h)
      = xor (aCountParityLens.view x) (aCountParityLens.view y) := by
  apply Raw.fold_slash
  intro u v
  show xor u v = xor v u
  cases u <;> cases v <;> rfl

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- canonicalTruthMap 의 specific reduction at a. -/
private theorem ctm_a : canonicalTruthMap Raw.a = True :=
  canonicalTruthMap_a

/-- canonicalTruthMap 의 specific reduction at b. -/
private theorem ctm_b : canonicalTruthMap Raw.b = False :=
  canonicalTruthMap_b

/-- propXor 의 Bool xor 와 의 connection. -/
theorem propXor_iff_bool_xor (P Q : Prop) (b₁ b₂ : Bool)
    (hP : P ↔ (b₁ = true)) (hQ : Q ↔ (b₂ = true)) :
    propXor P Q ↔ (xor b₁ b₂ = true) := by
  unfold propXor
  cases b₁ <;> cases b₂ <;> simp [xor, hP, hQ]

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Main characterization**: canonicalTruthMap r ↔ aCountParityLens.view r = true. -/
theorem canonicalTruthMap_iff_aCountOdd (r : Raw) :
    canonicalTruthMap r ↔ aCountParityLens.view r = true := by
  induction r using Raw.rec with
  | a =>
      rw [canonicalTruthMap_a, aCountParityLens_a]
      simp
  | b =>
      rw [canonicalTruthMap_b, aCountParityLens_b]
      simp
  | slash x y h ihx ihy =>
      rw [canonicalTruthMap_slash x y h, aCountParityLens_slash x y h]
      exact propXor_iff_bool_xor _ _ _ _ ihx ihy

end E213.Research.CanonicalTruthChar
