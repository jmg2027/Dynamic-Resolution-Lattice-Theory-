import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Hypervisor.Lens.Characterisation.Catalog

/-!
# Meta: R1–R4 typeclass hierarchy (4-tier `extends`)

Spec / Implementation separation for codomain candidates.

The R1–R4 conditions are split across **four classes**, each
extending the previous, so an instance can be partial (e.g.,
`R3Codomain` for non-self-recognising injective Lenses).
Generic theorems for each tier are proved once and inherited.

```
R12Codomain   ← R1 + R2: combine + commutativity
R3Codomain    ← +R3: no zero divisors
R4Codomain    ← +R4: nontrivial swap-matching involution
```

R5 is omitted (R5b is vacuous over inductive Raw — see
`E213.Research.R5Vacuity` and `notes/02_r5_vacuity.md`).
-/

namespace E213.Meta.SelfRecognising

open E213.Firmware E213.Hypervisor

-- ═══ Tier 1: R1 + R2 (binary commutative combine) ═══

class R12Codomain (α : Type) where
  base_a       : α
  base_b       : α
  combine      : α → α → α
  combine_comm : ∀ u v, combine u v = combine v u

namespace R12Codomain

variable {α : Type} [R12Codomain α]

/-- Generic Lens construction at the R12 tier. -/
def specLens : Lens α where
  base_a  := base_a (α := α)
  base_b  := base_b (α := α)
  combine := combine (α := α)

end R12Codomain

end E213.Meta.SelfRecognising

namespace E213.Meta.SelfRecognising

open E213.Firmware E213.Hypervisor R12Codomain
open E213.Hypervisor.Lens.Characterisation.Catalog

-- ═══ Tier 2: R3 (NonVanishing / no zero divisors) ═══

class R3Codomain (α : Type) [Zero α] extends R12Codomain α where
  base_a_ne_zero : R12Codomain.base_a (α := α) ≠ 0
  base_b_ne_zero : R12Codomain.base_b (α := α) ≠ 0
  no_zero_div    : ∀ u v : α, R12Codomain.combine u v = 0 → u = 0 ∨ v = 0

namespace R3Codomain

variable {α : Type} [Zero α] [R3Codomain α]

/-- **R3 (NonVanishing) — generic.** -/
theorem specLens_nonVanishing : NonVanishing (specLens (α := α)) :=
  fun u v hu hv hcomb => (no_zero_div u v hcomb).elim hu hv

end R3Codomain

-- ═══ Tier 3: R4 (SwapMatching with conjugation) ═══

class R4Codomain (α : Type) [Zero α] extends R3Codomain α where
  conj            : α → α
  conj_involution : ∀ u : α, conj (conj u) = u
  conj_ne_id      : conj ≠ id
  conj_dist       : ∀ u v : α, conj (R12Codomain.combine u v)
                                = R12Codomain.combine (conj u) (conj v)
  conj_swap_a     : conj (R12Codomain.base_a (α := α))
                       = R12Codomain.base_b (α := α)
  conj_swap_b     : conj (R12Codomain.base_b (α := α))
                       = R12Codomain.base_a (α := α)

namespace R4Codomain

variable {α : Type} [Zero α] [R4Codomain α]

/-- **R4 (SwapMatching) — generic.**  Uses `Raw.fold_swap_hom`. -/
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

end R4Codomain

end E213.Meta.SelfRecognising
