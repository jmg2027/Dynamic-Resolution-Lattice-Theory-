import E213.Research.SumInstance
import E213.Research.BoolPropMorphism

/-!
# Research.SumNotCoproduct: Sum α β 가 DistMorphism 의 coproduct
가 아님

PAPER1 §5.6, §9.4 의 open question 을 결정 적 으로 닫음:
priority-based combine 의 *non-canonicity* 를 형식 negative
result 로.

## 핵심 결과

`α = β = γ = Bool` with boolXor (xor combine).  f = g = id
는 양쪽 모두 HasDistinguishing morphism.

Coproduct universal property 가 만족 하려 면 unique
morphism `h : Sum Bool Bool → Bool` 이 존재 하 며 `h ∘ inl =
id`, `h ∘ inr = id`, AND `h` 가 combine 보존 해야 함.

**그런 h 부재**.  Counterexample: `(inl true, inr true)` 에서
`sumCombine = inl true` (priority left), 따라서
`h (sumCombine (inl true) (inr true)) = h (inl true) = true`.
하지만 `xor (h (inl true)) (h (inr true)) = xor true true =
false`.  Combine 보존 위반.

## 의의

Priority-based combine 은 *non-canonical*: DistMorphism
category 의 coproduct universal property 위반.  단순 valid
instance 일 뿐.  PAPER1 §5.6, §9.4 의 admitted asymmetry 가
formal negative theorem 으로 격상.
-/

namespace E213.Research.SumNotCoproduct

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.SumInstance
open E213.Research.BoolPropMorphism

/-- **Sum Bool Bool with xor 가 coproduct universal property
    위반**.  Counterexample: f = g = id 양쪽 morphism 인데, 그
    universal mediator h 가 combine 보존 불가. -/
theorem sum_not_coproduct_xor :
    ¬ ∃ h : Sum Bool Bool → Bool,
      (∀ x, h (Sum.inl x) = x) ∧
      (∀ x, h (Sum.inr x) = x) ∧
      (∀ x y, h (@sumCombine Bool Bool boolXorHasDistinguishing
                              boolXorHasDistinguishing x y)
              = xor (h x) (h y)) := by
  rintro ⟨h, hl, hr, hcomb⟩
  have h1 : h (Sum.inl true) = true := hl true
  have h2 : h (Sum.inr true) = true := hr true
  have h3 : @sumCombine Bool Bool boolXorHasDistinguishing
              boolXorHasDistinguishing (Sum.inl true) (Sum.inr true)
            = Sum.inl true := by
    unfold sumCombine; rfl
  have h4 := hcomb (Sum.inl true) (Sum.inr true)
  rw [h3] at h4
  rw [h1, h2] at h4
  -- h4 : true = xor true true.  xor true true = false → true = false → False
  simp at h4

end E213.Research.SumNotCoproduct
