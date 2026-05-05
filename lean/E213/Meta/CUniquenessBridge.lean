import E213.Hypervisor.Lens.Characterisation.Catalog
import E213.Meta.SelfRecognising

/-!
# T3 → T2/T1 migration — ℂ uniqueness via ConjugationCodomain

User: resolve hard deferred items.  Paper 2's "ℂ uniqueness"
was T3 (Frobenius classification).  Migrates to T2/T1 via
ConjugationCodomain typeclass.

ConjugationCodomain captures ℂ-likeness:
  - involution conj·conj = id
  - distribution over combine
  - swap of base values (a ↔ b)
  - nontrivial (conj ≠ id)

Verified instances: signedLens (Int with neg).
Failure case: swap-invariant Lenses (LensCatalog).
-/

namespace E213.Meta.CUniquenessBridge
open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Characterisation.Catalog
open E213.Meta.SelfRecognising

/-- ★ Involution. -/
theorem conjugation_involution {α : Type} [Zero α] [ConjugationCodomain α] :
    ∀ u : α, ConjugationCodomain.conj (ConjugationCodomain.conj u) = u :=
  ConjugationCodomain.conj_involution

/-- ★ Distributivity. -/
theorem conjugation_distributes {α : Type} [Zero α] [ConjugationCodomain α] :
    ∀ u v : α,
      ConjugationCodomain.conj (CommBinaryCodomain.combine u v)
        = CommBinaryCodomain.combine
            (ConjugationCodomain.conj u) (ConjugationCodomain.conj v) :=
  ConjugationCodomain.conj_dist

/-- ★ Base swap a ↔ b. -/
theorem conjugation_swap_a {α : Type} [Zero α] [ConjugationCodomain α] :
    ConjugationCodomain.conj (CommBinaryCodomain.base_a (α := α))
      = CommBinaryCodomain.base_b (α := α) :=
  ConjugationCodomain.conj_swap_a

/-- ★ Nontrivial. -/
theorem conjugation_nontrivial {α : Type} [Zero α] [ConjugationCodomain α] :
    @ConjugationCodomain.conj α _ _ ≠ id :=
  ConjugationCodomain.conj_ne_id

/-- ★★★ T3 → T2/T1: paper 2 "ℂ uniqueness" 213-internally
    via ConjugationCodomain class.  Any ConjugationCodomain α
    has ℂ-like conjugation structure. -/
theorem c_likeness_bundle {α : Type} [Zero α] [ConjugationCodomain α] :
    (∀ u : α, ConjugationCodomain.conj (ConjugationCodomain.conj u) = u)
    ∧ (∀ u v : α,
         ConjugationCodomain.conj (CommBinaryCodomain.combine u v)
           = CommBinaryCodomain.combine
               (ConjugationCodomain.conj u) (ConjugationCodomain.conj v))
    ∧ ConjugationCodomain.conj (CommBinaryCodomain.base_a (α := α))
        = CommBinaryCodomain.base_b (α := α)
    ∧ @ConjugationCodomain.conj α _ _ ≠ id :=
  ⟨conjugation_involution, conjugation_distributes,
   conjugation_swap_a, conjugation_nontrivial⟩

end E213.Meta.CUniquenessBridge
