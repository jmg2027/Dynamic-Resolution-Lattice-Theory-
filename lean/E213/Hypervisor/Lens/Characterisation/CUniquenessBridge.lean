import E213.Hypervisor.Lens.Characterisation.Catalog
import E213.Meta.SelfRecognising

/-!
# T3 → T2/T1 migration — ℂ uniqueness via R4Codomain

User: resolve hard deferred items.  Paper 2's "ℂ uniqueness"
was T3 (Frobenius classification).  Migrates to T2/T1 via
R4Codomain typeclass.

R4Codomain captures ℂ-likeness:
  - involution conj·conj = id
  - distribution over combine
  - swap of base values (a ↔ b)
  - nontrivial (conj ≠ id)

Verified instances: signedLens (Int with neg).
Failure case: swap-invariant Lenses (LensCatalog).
-/

namespace E213.Hypervisor.Lens.Characterisation.CUniquenessBridge
open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Characterisation.Catalog
open E213.Meta.SelfRecognising

/-- ★ Involution. -/
theorem r4_conj_involution {α : Type} [Zero α] [R4Codomain α] :
    ∀ u : α, R4Codomain.conj (R4Codomain.conj u) = u :=
  R4Codomain.conj_involution

/-- ★ Distributivity. -/
theorem r4_conj_distributes {α : Type} [Zero α] [R4Codomain α] :
    ∀ u v : α,
      R4Codomain.conj (R12Codomain.combine u v)
        = R12Codomain.combine
            (R4Codomain.conj u) (R4Codomain.conj v) :=
  R4Codomain.conj_dist

/-- ★ Base swap a ↔ b. -/
theorem r4_conj_swap_a {α : Type} [Zero α] [R4Codomain α] :
    R4Codomain.conj (R12Codomain.base_a (α := α))
      = R12Codomain.base_b (α := α) :=
  R4Codomain.conj_swap_a

/-- ★ Nontrivial. -/
theorem r4_conj_nontrivial {α : Type} [Zero α] [R4Codomain α] :
    @R4Codomain.conj α _ _ ≠ id :=
  R4Codomain.conj_ne_id

/-- ★★★ T3 → T2/T1: paper 2 "ℂ uniqueness" 213-internally
    via R4Codomain class.  Any R4Codomain α has ℂ-like
    conjugation structure. -/
theorem c_likeness_bundle {α : Type} [Zero α] [R4Codomain α] :
    (∀ u : α, R4Codomain.conj (R4Codomain.conj u) = u)
    ∧ (∀ u v : α,
         R4Codomain.conj (R12Codomain.combine u v)
           = R12Codomain.combine
               (R4Codomain.conj u) (R4Codomain.conj v))
    ∧ R4Codomain.conj (R12Codomain.base_a (α := α))
        = R12Codomain.base_b (α := α)
    ∧ @R4Codomain.conj α _ _ ≠ id :=
  ⟨r4_conj_involution, r4_conj_distributes,
   r4_conj_swap_a, r4_conj_nontrivial⟩

end E213.Hypervisor.Lens.Characterisation.CUniquenessBridge