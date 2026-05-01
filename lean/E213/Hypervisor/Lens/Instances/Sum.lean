import E213.Hypervisor.Lens.SemanticAtom
import E213.Hypervisor.Lens.Instances.Reach

/-!
# Research.SumInstance: priority-based combine instance for Sum type

User directive (2026-04-25): Direct attack on coproduct — Prism-like
dual structure.

HasDistinguishing instance for `Sum α β` — combine is defined as
priority-based (left preference).  No natural answer in the mixed case
but formalizable with commutative + distinct preservation.

## Definition of combine

```
combine (inl a) (inl a') = inl (d_α.combine a a')  -- both left
combine (inr b) (inr b') = inr (d_β.combine b b')  -- both right
combine (inl a) (inr _)  = inl a                   -- mixed: prefer left
combine (inr _) (inl a)  = inl a                   -- sym
```

The priority in the mixed case is ad-hoc — not *fully aligned* with the
natural universal property of categorical coproduct.  Just a valid instance.

## Significance

Sum type is also an instance of the framework — however, the priority in
the mixed case is an *artificial choice* (not categorically natural).
This is the categorical limit of the framework — the universal property
of coproduct does not naturally emerge in 213's distinguishing-framework
category.

(The image of universalMorphism for this instance has specific algebraic
content — interesting to analyze.)
-/

namespace E213.Hypervisor.Lens.Instances.Sum

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom
open E213.Hypervisor.Lens.InstancesReach

/-- Priority-based combine for Sum type. -/
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

end E213.Hypervisor.Lens.Instances.Sum

namespace E213.Hypervisor.Lens.Instances.Sum

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom

/-- HasDistinguishing instance for Sum type. -/
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

end E213.Hypervisor.Lens.Instances.Sum
