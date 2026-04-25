import E213.Research.SemanticAtom

/-!
# Research.InstanceReach: universalMorphism 의 image 의 boundary

`SemanticAtom.lean` 의 `universalMorphism α : Raw → α` 가
HasDistinguishing instance α 의 morphism.  이 image 가 *항상*
α 와 같은 가? — 답: **아님**.  α 의 carrier 가 image 보다 더
클 수 있음.

## 의의

의미 atom thesis 의 sharpening:

> Raw 가 모든 distinguishing-framework instance 의 *generator*
> (image 가 distinguishing-closed sub-instance).  하지만 instance
> 의 carrier 가 image 보다 *strict 클* 수 있음 — framework 의
> reach 와 carrier 의 분리.

즉 의미 atom 이 generator 의 minimum 이고, instance 가 그 위
"unreachable" element 를 carry 가능.  이게 framework 의 *reach
boundary* 의 명시.

## Witness

`Fin 3` with `a := 0, b := 1, combine := λ _ _, 0`:
- reach = {0, 1} (Raw 로 부터 image).
- carrier = {0, 1, 2}.
- 2 ∉ image — strict subset.

Note 80 분석.
-/

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Witness: Fin 3 의 trivial-combine instance -/

instance fin3HasDistinguishing : HasDistinguishing (Fin 3) where
  a := 0
  b := 1
  distinct := by decide
  combine _ _ := 0
  combine_sym _ _ := rfl

/-- Image 의 forward closure: universalMorphism (Fin 3) 의 결과
    가 항상 0 또는 1 (combine 이 항상 0). -/
theorem fin3_image_in_01 (r : Raw) :
    universalMorphism (Fin 3) r = 0 ∨ universalMorphism (Fin 3) r = 1 := by
  induction r using Raw.rec with
  | a => left; exact universalMorphism_a (Fin 3)
  | b => right; exact universalMorphism_b (Fin 3)
  | slash x y h _ _ =>
      left
      rw [universalMorphism_slash (Fin 3) x y h]
      rfl

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Image 의 strict subset**: Fin 3 의 element 2 가 universalMorphism
    의 image 외부.  framework 의 reach 와 carrier 의 분리 의 명시
    적 witness. -/
theorem fin3_image_strict :
    ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x := by
  refine ⟨2, ?_⟩
  intro ⟨r, hr⟩
  rcases fin3_image_in_01 r with h | h
  · rw [h] at hr; exact absurd hr (by decide)
  · rw [h] at hr; exact absurd hr (by decide)

end E213.Research.InstanceReach
