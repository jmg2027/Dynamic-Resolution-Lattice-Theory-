import E213.Hypervisor.Lens.Research.Instance.Sum
import E213.Hypervisor.Lens.Research.Morphism.BoolProp

/-!
# Research.SumNotCoproductGeneric: generic case of Sum α β coproduct failure

Extends the xor case of `SumNotCoproduct` to other commutative combines.
The non-canonicity of Sum α β + priority combine is not `xor`-specific
but a *broad phenomenon*.

## Core

`α = β = γ = Bool` with **and** combine: f = g = id are both morphisms,
but no mediating h exists.

Counterexample: combine (inl true) (inr false) = inl true (priority).
`h(inl true) = true`, `h(inr false) = false`.
But morphism requires: `h (combine ...) = and (h ...) (h ...)` =
and true false = false.  Contradiction (true ≠ false).
-/

namespace E213.Hypervisor.Lens.Research.Instance.SumNotCoproductGeneric

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.SumInstance
open E213.Research.BoolPropMorphism

/-- Sum Bool Bool with **and** combine (boolXorHasDistinguishing
    used as instance for both sides) also violates the coproduct
    universal property. -/
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

end E213.Hypervisor.Lens.Research.Instance.SumNotCoproductGeneric
