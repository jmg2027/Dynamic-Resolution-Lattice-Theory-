import E213.Lens.Foundations.SemanticAtom
import E213.Lens.Instances.Reach

/-!
# PairInstance: categorical product of HasDistinguishing

`α × β` is a HasDistinguishing instance — the categorical product of
two instances.  universalMorphism splits componentwise as a fold.

## Results

- `pairHasDistinguishing α β`: pair instance.
- `universalMorphism_pair_commute`: universalMorphism (α × β)
  = (universalMorphism α, universalMorphism β) componentwise.

This is the universal property of the *binary product* in the
distinguishing-framework category — the product structure of semantic
atoms.
-/

namespace E213.Lens.Instances.Pair

open E213.Theory E213.Lens
open E213.Lens.Foundations.SemanticAtom

/-- Pair instance: the product of two HasDistinguishing instances. -/
def pairHasDistinguishing (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : HasDistinguishing (α × β) where
  a := (d_α.a, d_β.a)
  b := (d_α.b, d_β.b)
  distinct := fun h => d_α.distinct (congrArg Prod.fst h)
  combine := fun p q => (d_α.combine p.1 q.1, d_β.combine p.2 q.2)
  same := fun p q => d_α.same p.1 q.1 ∧ d_β.same p.2 q.2
  same_refl := fun p => ⟨d_α.same_refl p.1, d_β.same_refl p.2⟩
  same_symm := fun h => ⟨d_α.same_symm h.1, d_β.same_symm h.2⟩
  same_trans := fun h1 h2 => ⟨d_α.same_trans h1.1 h2.1, d_β.same_trans h1.2 h2.2⟩
  combine_sym := fun p q => ⟨d_α.combine_sym p.1 q.1, d_β.combine_sym p.2 q.2⟩
  combine_cong := fun _ _ _ _ ha hb =>
    ⟨d_α.combine_cong _ _ _ _ ha.1 hb.1, d_β.combine_cong _ _ _ _ ha.2 hb.2⟩


/-- **Universal property of binary product**: universalMorphism (α × β)
    is the pair of componentwise universalMorphisms — up to the product
    reading-sameness (at `Eq` components this is literal pair equality).
    Proven via `universalMorphism_unique` (componentwise homomorphism). -/
theorem universalMorphism_pair_commute (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    (pairHasDistinguishing α β).same
      (@universalMorphism (α × β) (pairHasDistinguishing α β) r)
      (universalMorphism α r, universalMorphism β r) :=
  (pairHasDistinguishing α β).same_symm
    (universalMorphism_unique (α × β) (d := pairHasDistinguishing α β)
      (fun r => (universalMorphism α r, universalMorphism β r))
      ((pairHasDistinguishing α β).same_refl _)
      ((pairHasDistinguishing α β).same_refl _)
      (fun x y h => ⟨universalMorphism_slash α x y h, universalMorphism_slash β x y h⟩)
      r)


/-! ### Pair forget projections (categorical projection morphisms)

`α × β → α` and `α × β → β` are *projections* in the
distinguishing-framework category — part of the universal property of
the categorical product.

Written as direct records since typeclass synthesis for `DistMorphism`
is absent.
-/

/-- Properties of the pair forget projection α × β → α. -/
theorem pair_forget_first_a (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.fst (pairHasDistinguishing α β).a = d_α.a := rfl

theorem pair_forget_first_b (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.fst (pairHasDistinguishing α β).b = d_α.b := rfl

theorem pair_forget_first_combine (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (p q : α × β) :
    Prod.fst ((pairHasDistinguishing α β).combine p q)
      = d_α.combine (Prod.fst p) (Prod.fst q) := rfl

theorem pair_forget_second_a (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.snd (pairHasDistinguishing α β).a = d_β.a := rfl

theorem pair_forget_second_b (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.snd (pairHasDistinguishing α β).b = d_β.b := rfl

theorem pair_forget_second_combine (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (p q : α × β) :
    Prod.snd ((pairHasDistinguishing α β).combine p q)
      = d_β.combine (Prod.snd p) (Prod.snd q) := rfl


/-! ### Combination of universal property and forget projections

The first/second projection of universalMorphism (α × β) equals the
componentwise universalMorphism — a direct consequence of the
universal property of the categorical product. -/

theorem universalMorphism_first (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    d_α.same (Prod.fst (@universalMorphism (α × β) (pairHasDistinguishing α β) r))
      (universalMorphism α r) :=
  (universalMorphism_pair_commute α β r).1

theorem universalMorphism_second (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    d_β.same (Prod.snd (@universalMorphism (α × β) (pairHasDistinguishing α β) r))
      (universalMorphism β r) :=
  (universalMorphism_pair_commute α β r).2

end E213.Lens.Instances.Pair
