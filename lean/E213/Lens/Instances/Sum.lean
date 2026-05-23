import E213.Lens.SemanticAtom
import E213.Lens.Instances.Reach

/-!
# SumInstance: priority-based combine instance for Sum type

User directive: Direct attack on coproduct — Prism-like
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

namespace E213.Lens.Instances.Sum

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

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
  cases x with
  | inl a => cases y with
    | inl b =>
        show Sum.inl (d_α.combine a b) = Sum.inl (d_α.combine b a)
        rw [d_α.combine_sym]
    | inr _ => rfl
  | inr a => cases y with
    | inl _ => rfl
    | inr b =>
        show Sum.inr (d_β.combine a b) = Sum.inr (d_β.combine b a)
        rw [d_β.combine_sym]


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

end E213.Lens.Instances.Sum
