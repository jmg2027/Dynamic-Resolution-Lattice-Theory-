import E213.Math.Cohomology.Universal.Core.Prop51
import E213.Math.Cohomology.Universal.Core.Prop52
import E213.Math.Cohomology.Universal.Core.Prop53
import E213.Math.Cohomology.Hodge.Prop
import E213.Math.Cohomology.Hodge.Prop52
import E213.Math.Cohomology.CupAW.Leibniz
import E213.Math.Cohomology.EncodingBijection

/-!
# Δ⁴ Cohomology — Prop-level capstone bundle

  1. δ²=0 universal at (5, k) for k = 1, 2, 3
  2. ⋆⋆=id universal at (5, k) for k = 1, 2
  3. Cup Leibniz universal (AW overlap) at (5, 1, 1)
  4. Encoding bijection: Cochain 5 1 ↔ Fin 32

≤ {propext, Quot.sound}.
-/

namespace E213.Math.Cohomology.Delta.Core.V4Capstone

open E213.Physics.Simplex (binom)

/-- ★★★ Δ⁴ Universal δ²=0 over all interior strata. -/
theorem dsq_zero_universal_delta4 :
    (∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 3),
       delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 4),
         delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 5),
         delta (delta σ) i = false) :=
  ⟨UniversalProp51.dsq_zero_prop_5_1,
   UniversalProp52.dsq_zero_prop_5_2,
   UniversalProp53.dsq_zero_prop_5_3⟩

/-- ★★★ Δ⁴ Universal Hodge involution ⋆⋆=id. -/
theorem hodge_involution_universal_delta4 :
    (∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
       hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
         hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i) :=
  ⟨HodgeProp.hodge_sq_prop_5_1,
   HodgeProp52.hodge_sq_prop_5_2⟩

/-- ★★★ Cup Leibniz universal (AW cup). -/
theorem leibniz_universal_delta4 :
    ∀ α β : Cochain 5 1, ∀ i : Fin (binom 5 2),
      delta (cupAW 5 1 1 α β) i
        = xor (cupAW 5 2 1 (delta α) β i)
              (cupAW 5 1 2 α (delta β) i) :=
  CupAWLeibniz.leibniz_universal_5_1_1

/-- ★★★ Encoding bijection at (5, 1). -/
theorem encoding_bijection_delta4 :
    ∀ σ : Cochain 5 1, ∀ j : Fin 5,
      σ j = cochainAt 5 1 (EncodingBijection.encode_5_1 σ) j :=
  EncodingBijection.encode_bijection

/-- ★★★★★ Δ⁴ Cohomology capstone — full Prop-level lift of
    cohomology axioms on the atomic substrate. -/
theorem delta4_cohomology_capstone :
    (∀ σ : Cochain 5 1, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 2, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 3, ∀ i, delta (delta σ) i = false)
    ∧ (∀ σ : Cochain 5 1, ∀ i,
         hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 2, ∀ i,
         hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i)
    ∧ (∀ α β : Cochain 5 1, ∀ i,
         delta (cupAW 5 1 1 α β) i
           = xor (cupAW 5 2 1 (delta α) β i)
                 (cupAW 5 1 2 α (delta β) i)) :=
  ⟨UniversalProp51.dsq_zero_prop_5_1,
   UniversalProp52.dsq_zero_prop_5_2,
   UniversalProp53.dsq_zero_prop_5_3,
   HodgeProp.hodge_sq_prop_5_1,
   HodgeProp52.hodge_sq_prop_5_2,
   CupAWLeibniz.leibniz_universal_5_1_1⟩

end E213.Math.Cohomology.Delta.Core.V4Capstone
