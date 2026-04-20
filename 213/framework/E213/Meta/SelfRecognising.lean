import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Meta.LensCatalog

/-!
# Meta: `SelfRecognisingCodomain` — the R1–R4 spec

Spec / Implementation separation for codomain candidates.

A codomain `α` that wants to provide a self-recognising Lens
(R1–R4 satisfied) must implement this type class.  Each
instance carries the **proofs** (implementation); downstream
generic theorems consume the spec without seeing them.

Once an instance is provided, `specLens α` is the corresponding
Lens, `specLens_nonVanishing` is R3, and
`specLens_swapMatching` is R4 — both proved once at the
abstract level via `Raw.fold_swap_hom`.
-/

namespace E213.Meta

open E213.Firmware E213.Hypervisor

/-- **Spec.** A codomain `α` satisfies R1–R4 if it carries
    base values, a commutative no-zero-divisor combine, and a
    nontrivial involution `conj` swapping the base values and
    distributing over combine. -/
class SelfRecognisingCodomain (α : Type) [Zero α] where
  base_a       : α
  base_b       : α
  combine      : α → α → α
  conj         : α → α
  base_a_ne_zero  : base_a ≠ 0
  base_b_ne_zero  : base_b ≠ 0
  combine_comm    : ∀ u v, combine u v = combine v u
  no_zero_div     : ∀ u v, combine u v = 0 → u = 0 ∨ v = 0
  conj_involution : ∀ u, conj (conj u) = u
  conj_ne_id      : conj ≠ id
  conj_dist       : ∀ u v, conj (combine u v) = combine (conj u) (conj v)
  conj_swap_a     : conj base_a = base_b
  conj_swap_b     : conj base_b = base_a

namespace SelfRecognisingCodomain

variable {α : Type} [Zero α] [SelfRecognisingCodomain α]

/-- **Generic Lens.** Use `specLens α` once the spec is
    instantiated; downstream theorems take it from here. -/
def specLens : Lens α where
  base_a  := base_a (α := α)
  base_b  := base_b (α := α)
  combine := combine (α := α)

/-- **R3 (NonVanishing) — generic.**  Follows immediately from
    the spec's `no_zero_div`. -/
theorem specLens_nonVanishing : NonVanishing (specLens (α := α)) := by
  intro u v hu hv hcomb
  rcases no_zero_div u v hcomb with h | h
  · exact hu h
  · exact hv h

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

end SelfRecognisingCodomain

end E213.Meta
