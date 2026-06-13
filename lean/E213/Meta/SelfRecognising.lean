import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Properties

/-!
# Meta: codomain typeclass hierarchy (3-tier `extends`)

Spec / Implementation separation for codomain candidates.

The conditions are split across **three classes**, each
extending the previous, so an instance can be partial (e.g.,
`NonVanishingCodomain` for non-self-recognising injective Lenses).
Generic theorems for each tier are proved once and inherited.

```
CommBinaryCodomain   ← commutative binary combine
NonVanishingCodomain ← + no zero divisors
ConjugationCodomain  ← + nontrivial swap-matching involution
```

The three typeclasses are a generic codomain spec — commutative
combine, no zero divisors, nontrivial swap-matching involution —
independent of any particular carrier.
-/

namespace E213.Meta.SelfRecognising

open E213.Theory E213.Lens

-- ═══ Tier 1: commutative binary combine ═══

class CommBinaryCodomain (α : Type) where
  base_a       : α
  base_b       : α
  combine      : α → α → α
  combine_comm : ∀ u v, combine u v = combine v u

namespace CommBinaryCodomain

variable {α : Type} [CommBinaryCodomain α]

/-- Generic Lens construction at the commutative-binary tier. -/
def specLens : Lens α where
  base_a  := base_a (α := α)
  base_b  := base_b (α := α)
  combine := combine (α := α)

end CommBinaryCodomain


open E213.Theory E213.Lens CommBinaryCodomain
open E213.Lens.Properties.Characterisation.Catalog

-- ═══ Tier 2: NonVanishing (no zero divisors) ═══

class NonVanishingCodomain (α : Type) [Zero α] extends CommBinaryCodomain α where
  base_a_ne_zero : CommBinaryCodomain.base_a (α := α) ≠ 0
  base_b_ne_zero : CommBinaryCodomain.base_b (α := α) ≠ 0
  no_zero_div    : ∀ u v : α, CommBinaryCodomain.combine u v = 0 → u = 0 ∨ v = 0

namespace NonVanishingCodomain

variable {α : Type} [Zero α] [NonVanishingCodomain α]

/-- **NonVanishing — generic.** -/
theorem specLens_nonVanishing : NonVanishing (specLens (α := α)) :=
  fun u v hu hv hcomb => (no_zero_div u v hcomb).elim hu hv

end NonVanishingCodomain

-- ═══ Tier 3: Conjugation (SwapMatching with involution) ═══

class ConjugationCodomain (α : Type) [Zero α] extends NonVanishingCodomain α where
  conj            : α → α
  conj_involution : ∀ u : α, conj (conj u) = u
  /-- Non-trivial witness: some element where `conj` does not fix.
      Point-wise form (`∃` rather than `conj ≠ id`) keeps downstream
      `SwapMatching` consumers funext-free. -/
  conj_ne_id      : ∃ x, conj x ≠ x
  conj_dist       : ∀ u v : α, conj (CommBinaryCodomain.combine u v)
                                = CommBinaryCodomain.combine (conj u) (conj v)
  conj_swap_a     : conj (CommBinaryCodomain.base_a (α := α))
                       = CommBinaryCodomain.base_b (α := α)
  conj_swap_b     : conj (CommBinaryCodomain.base_b (α := α))
                       = CommBinaryCodomain.base_a (α := α)

namespace ConjugationCodomain

variable {α : Type} [Zero α] [ConjugationCodomain α]

/-- **SwapMatching — generic.**  Uses `Raw.fold_swap_hom`. -/
theorem specLens_swapMatching :
    SwapMatching (specLens (α := α)) (conj (α := α)) := by
  refine ⟨conj_involution, conj_ne_id, ?_⟩
  intro r
  show Raw.fold (base_a (α := α)) (base_b (α := α))
        (combine (α := α)) (Raw.swap r)
     = conj (Raw.fold (base_a (α := α)) (base_b (α := α))
        (combine (α := α)) r)
  exact Raw.fold_swap_hom _ _ _ _ conj_swap_a conj_swap_b
    conj_dist combine_comm r

end ConjugationCodomain

end E213.Meta.SelfRecognising
