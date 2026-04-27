import E213.Math.Cohomology.CupLeibniz

/-!
# Cohomology — ring structure on H* (Phase CD, file 3)

Cup makes H*(Δⁿ⁻¹) into a graded-commutative ring.  We verify
the key identities at concrete cochains on Δ⁴ (n=5):

  * Unit: ε ∈ C⁰ = `fun _ => true` is left and right identity.
  * Associativity: (α ⌣ β) ⌣ γ = α ⌣ (β ⌣ γ).
  * In ℤ/2 graded-commutativity collapses to commutativity (sign
    (-1)^(kl) is always 1).

Universal-∀ versions deferred (Fintype/DecidablePred constraint
discussed in Phase CB lessons).
-/

namespace E213.Math.Cohomology

open E213.Physics.Simplex (binom d NS NT)

/-- Multiplicative unit at (n=5, k=0): true on the unique 0-subset. -/
def unit_5 : Cochain 5 0 := fun _ => true

/-- Left unit: ε ⌣ v0_5 = v0_5. -/
theorem cup_unit_left_v0 :
    ∀ i : Fin (binom 5 1),
      cup 5 0 1 unit_5 v0_5 i = v0_5 i := by decide

/-- Right unit: v0_5 ⌣ ε = v0_5. -/
theorem cup_unit_right_v0 :
    ∀ i : Fin (binom 5 1),
      cup 5 1 0 v0_5 unit_5 i = v0_5 i := by decide

/-- Left unit: ε ⌣ all_true_5_1 = all_true_5_1. -/
theorem cup_unit_left_all_true :
    ∀ i : Fin (binom 5 1),
      cup 5 0 1 unit_5 all_true_5_1 i = all_true_5_1 i := by decide

/-- Associativity at all-true ⌣ all-true ⌣ all-true on C¹⁺¹⁺¹=C³. -/
theorem cup_assoc_all_true :
    ∀ i : Fin (binom 5 3),
      cup 5 2 1 (cup 5 1 1 all_true_5_1 all_true_5_1) all_true_5_1 i
        = cup 5 1 2 all_true_5_1 (cup 5 1 1 all_true_5_1 all_true_5_1) i := by
  decide

/-- Associativity at v0 ⌣ all_true ⌣ all_true. -/
theorem cup_assoc_v0_at_at :
    ∀ i : Fin (binom 5 3),
      cup 5 2 1 (cup 5 1 1 v0_5 all_true_5_1) all_true_5_1 i
        = cup 5 1 2 v0_5 (cup 5 1 1 all_true_5_1 all_true_5_1) i := by decide

/-- Cochain-level non-commutativity (Alexander–Whitney is not
    symmetric in α, β at cochain level).  Graded-commutativity
    holds only on H*, modulo coboundaries δ(...) — formalising
    that requires the quotient C/δC, deferred. -/
theorem cup_not_pointwise_comm :
    cup 5 1 1 all_true_5_1 v0_5 ⟨0, by decide⟩
      ≠ cup 5 1 1 v0_5 all_true_5_1 ⟨0, by decide⟩ := by decide

/-- ★ Phase CD capstone — H* ring structure on Δ⁴ verified at
    cochain level: unit (left + right), associativity at two
    cochain triples.  Plus the honest negative result that
    cup is *not* commutative as cochains (only on H*). -/
theorem phase_CD_capstone :
    (∀ i : Fin (binom 5 1), cup 5 0 1 unit_5 v0_5 i = v0_5 i)
    ∧ (∀ i : Fin (binom 5 1), cup 5 1 0 v0_5 unit_5 i = v0_5 i)
    ∧ (∀ i : Fin (binom 5 3),
         cup 5 2 1 (cup 5 1 1 all_true_5_1 all_true_5_1) all_true_5_1 i
           = cup 5 1 2 all_true_5_1 (cup 5 1 1 all_true_5_1 all_true_5_1) i)
    ∧ (cup 5 1 1 all_true_5_1 v0_5 ⟨0, by decide⟩
         ≠ cup 5 1 1 v0_5 all_true_5_1 ⟨0, by decide⟩) :=
  ⟨cup_unit_left_v0, cup_unit_right_v0, cup_assoc_all_true,
   cup_not_pointwise_comm⟩

end E213.Math.Cohomology
