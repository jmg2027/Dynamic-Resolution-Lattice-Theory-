import E213.Research.SemanticAtom
import E213.Research.InstanceReach

/-!
# Research.SumInstance: Sum type 의 priority-based combine instance

User directive (2026-04-25): Coproduct 의 정면 돌파 — Prism-like
dual 구조.

`Sum α β` 의 HasDistinguishing instance — combine 의 정의 가
priority-based (left preference).  Mixed case 의 자연 한 답 부재
이지만 commutative + distinct 보존 으로 형식 가능.

## combine 의 정의

```
combine (inl a) (inl a') = inl (d_α.combine a a')  -- both left
combine (inr b) (inr b') = inr (d_β.combine b b')  -- both right
combine (inl a) (inr _)  = inl a                   -- mixed: prefer left
combine (inr _) (inl a)  = inl a                   -- sym
```

Mixed case 의 priority 가 ad-hoc — categorical coproduct 의 자연
universal property 와 *완전 align* 부재.  단지 valid instance.

## 의의

Sum type 도 framework 의 instance — 단, mixed case 의 priority
가 *artificial choice* (not categorically natural).  이게 framework
의 categorical limit — coproduct 의 universal property 가 213 의
distinguishing-framework category 에서 정확 히 emerge 부재.

(이 instance 의 universalMorphism 의 image 가 specific algebraic
content — 분석 흥미.)
-/

namespace E213.Research.SumInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-- Sum type 의 priority-based combine. -/
def sumCombine {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x y : Sum α β) : Sum α β :=
  match x, y with
  | Sum.inl a, Sum.inl a' => Sum.inl (d_α.combine a a')
  | Sum.inr b, Sum.inr b' => Sum.inr (d_β.combine b b')
  | Sum.inl a, Sum.inr _ => Sum.inl a
  | Sum.inr _, Sum.inl a => Sum.inl a

theorem sumCombine_comm {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x y : Sum α β) :
    sumCombine x y = sumCombine y x := by
  cases x <;> cases y <;> simp [sumCombine, d_α.combine_sym, d_β.combine_sym]

end E213.Research.SumInstance

namespace E213.Research.SumInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Sum type 의 HasDistinguishing instance. -/
def sumHasDistinguishing (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : HasDistinguishing (Sum α β) where
  a := Sum.inl d_α.a
  b := Sum.inr d_β.b
  distinct := fun h => Sum.noConfusion h
  combine := sumCombine
  combine_sym := sumCombine_comm

/-- Universal morphism Raw → Sum α β. -/
def sumUniversalMorphism (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : Raw → Sum α β :=
  @universalMorphism (Sum α β) (sumHasDistinguishing α β)

end E213.Research.SumInstance
