import E213.Lens.Instances.Sum
import E213.Lens.Morphism.BoolProp

/-!
# SumNotCoproduct: Sum α β is not a coproduct of DistMorphism

Decisively closes the open question of PAPER1 §5.6, §9.4:
*non-canonicity* of priority-based combine as a formal negative result.

## Core result

`α = β = γ = Bool` with boolXor (xor combine).  f = g = id
are both HasDistinguishing morphisms.

For the coproduct universal property to hold, a unique morphism
`h : Sum Bool Bool → Bool` must exist with `h ∘ inl = id`,
`h ∘ inr = id`, AND `h` preserving combine.

**No such h exists**.  Counterexample: at `(inl true, inr true)`,
`sumCombine = inl true` (priority left), so
`h (sumCombine (inl true) (inr true)) = h (inl true) = true`.
But `xor (h (inl true)) (h (inr true)) = xor true true = false`.
Combine preservation violated.

## Significance

Priority-based combine is *non-canonical*: it violates the coproduct
universal property of the DistMorphism category.  It is merely a valid
instance.  The admitted asymmetry in PAPER1 §5.6, §9.4 is elevated to
a formal negative theorem.
-/

namespace E213.Lens.Instances.SumNotCoproduct

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Sum
open E213.Lens.Morphism.BoolProp

/-- **Sum Bool Bool with xor violates the coproduct universal property**.
    Counterexample: f = g = id are both morphisms, but no universal
    mediator h can preserve combine. -/
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

end E213.Lens.Instances.SumNotCoproduct
