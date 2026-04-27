import E213.Research.SumInstance
import E213.Research.BoolPropMorphism

/-!
# Research.SumNotCoproductGeneric: Sum α β coproduct failure 의
generic case

`SumNotCoproduct` 의 xor case 를 다른 commutative combine 으 로
확장.  Sum α β + priority combine 의 non-canonicity 가 `xor`
specific 이 아 니 라 *broad phenomenon*.

## 핵심

`α = β = γ = Bool` with **and** combine: f = g = id 양쪽
morphism 인데, mediating h 부재.

Counterexample: combine (inl true) (inr false) = inl true
(priority).  `h(inl true) = true`, `h(inr false) = false`.
But morphism 요구: `h (combine ...) = and (h ...) (h ...)` =
and true false = false.  Contradiction (true ≠ false).
-/

namespace E213.Research.SumNotCoproductGeneric

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.SumInstance
open E213.Research.BoolPropMorphism

/-- Sum Bool Bool with **and** combine (boolXorHasDistinguishing
    used as instance for both sides) 도 coproduct universal
    property 위반. -/
theorem sum_not_coproduct_and :
    ¬ ∃ h : Sum Bool Bool → Bool,
      (∀ x, h (Sum.inl x) = x) ∧
      (∀ x, h (Sum.inr x) = x) ∧
      (∀ x y, h (@sumCombine Bool Bool boolXorHasDistinguishing
                              boolXorHasDistinguishing x y)
              = (h x && h y)) := by
  rintro ⟨h, hl, hr, hcomb⟩
  have h1 : h (Sum.inl true) = true := hl true
  have h2 : h (Sum.inr false) = false := hr false
  have h3 : @sumCombine Bool Bool boolXorHasDistinguishing
              boolXorHasDistinguishing (Sum.inl true) (Sum.inr false)
            = Sum.inl true := by
    unfold sumCombine; rfl
  have h4 := hcomb (Sum.inl true) (Sum.inr false)
  rw [h3] at h4
  rw [h1, h2] at h4
  simp at h4

end E213.Research.SumNotCoproductGeneric
