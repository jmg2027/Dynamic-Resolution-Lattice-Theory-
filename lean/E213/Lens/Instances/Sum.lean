import E213.Lens.Foundations.SemanticAtom
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
open E213.Lens.Foundations.SemanticAtom
open E213.Lens.Instances.Reach

/-- Priority-based combine for Sum type. -/
def sumCombine {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x y : Sum α β) : Sum α β :=
  match x, y with
  | Sum.inl a, Sum.inl a' => Sum.inl (d_α.combine a a')
  | Sum.inr b, Sum.inr b' => Sum.inr (d_β.combine b b')
  | Sum.inl a, Sum.inr _ => Sum.inl a
  | Sum.inr _, Sum.inl a => Sum.inl a

/-- Reading-sameness for `Sum α β`: componentwise on matching constructors,
    `False` on mixed (`inl`/`inr` are distinguished).  Coincides with `=` when
    both components' `same` are `Eq`. -/
def sumSame {α β : Type} [d_α : HasDistinguishing α] [d_β : HasDistinguishing β]
    (x y : Sum α β) : Prop :=
  match x, y with
  | Sum.inl a, Sum.inl a' => d_α.same a a'
  | Sum.inr b, Sum.inr b' => d_β.same b b'
  | _, _ => False

theorem sumSame_refl {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x : Sum α β) : sumSame x x := by
  cases x with
  | inl a => exact d_α.same_refl a
  | inr b => exact d_β.same_refl b

theorem sumSame_symm {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] {x y : Sum α β} : sumSame x y → sumSame y x := by
  cases x <;> cases y <;> intro h <;>
    first
      | exact d_α.same_symm h
      | exact d_β.same_symm h
      | exact h.elim

theorem sumSame_trans {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] {x y z : Sum α β} :
    sumSame x y → sumSame y z → sumSame x z := by
  cases x <;> cases y <;> cases z <;> intro h1 h2 <;>
    first
      | exact d_α.same_trans h1 h2
      | exact d_β.same_trans h1 h2
      | exact h1.elim
      | exact h2.elim

theorem sumCombine_comm {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (x y : Sum α β) :
    sumSame (sumCombine x y) (sumCombine y x) := by
  cases x <;> cases y <;>
    first
      | exact d_α.combine_sym _ _
      | exact d_β.combine_sym _ _
      | exact d_α.same_refl _
      | exact d_β.same_refl _

theorem sumCombine_cong {α β : Type} [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] (a a' b b' : Sum α β)
    (ha : sumSame a a') (hb : sumSame b b') :
    sumSame (sumCombine a b) (sumCombine a' b') := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    first
      | exact d_α.combine_cong _ _ _ _ ha hb
      | exact d_β.combine_cong _ _ _ _ ha hb
      | exact ha
      | exact hb
      | exact ha.elim
      | exact hb.elim


/-- HasDistinguishing instance for Sum type. -/
def sumHasDistinguishing (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : HasDistinguishing (Sum α β) where
  a := Sum.inl d_α.a
  b := Sum.inr d_β.b
  distinct := fun h => Sum.noConfusion h
  combine := sumCombine
  same := sumSame
  same_refl := sumSame_refl
  same_symm := sumSame_symm
  same_trans := sumSame_trans
  combine_sym := sumCombine_comm
  combine_cong := sumCombine_cong

/-- Universal morphism Raw → Sum α β. -/
def sumUniversalMorphism (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : Raw → Sum α β :=
  @universalMorphism (Sum α β) (sumHasDistinguishing α β)

end E213.Lens.Instances.Sum
