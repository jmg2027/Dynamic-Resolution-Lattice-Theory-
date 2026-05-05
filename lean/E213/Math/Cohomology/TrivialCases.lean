import E213.Math.Cohomology.Delta.SqZero

/-!
# Cohomology — capstone: smoke tests across d ≤ 5 (file 5)

Verifies that the cochain complex `(Cᵏ, δ)` on Δⁿ⁻¹ is well-formed
for n = 2, 3, 4, 5.  Each row checks face counts + that δ preserves
the zero cochain.  All theorems 0-axiom, `decide`-checked.
-/

namespace E213.Math.Cohomology.TrivialCases

open E213.Physics.Simplex.Counts (binom d NS NT)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Core (delta)

/-! ## Δ¹ (n=2) -/

theorem dim_n2 :
    binom 2 0 = 1 ∧ binom 2 1 = 2 ∧ binom 2 2 = 1 := by decide

theorem delta_zero_preserves_zero_2_0 :
    ∀ i : Fin (binom 2 1), delta (Cochain.zero 2 0) i = false := by decide

/-! ## Δ² (n=3) -/

theorem dim_n3 :
    binom 3 0 = 1 ∧ binom 3 1 = 3 ∧ binom 3 2 = 3 ∧ binom 3 3 = 1 := by decide

theorem delta_zero_preserves_zero_3_0 :
    ∀ i : Fin (binom 3 1), delta (Cochain.zero 3 0) i = false := by decide

theorem delta_zero_preserves_zero_3_1 :
    ∀ i : Fin (binom 3 2), delta (Cochain.zero 3 1) i = false := by decide

/-! ## Δ³ (n=4) -/

theorem dim_n4 :
    binom 4 0 = 1 ∧ binom 4 1 = 4 ∧ binom 4 2 = 6
    ∧ binom 4 3 = 4 ∧ binom 4 4 = 1 := by decide

theorem delta_zero_preserves_zero_4_1 :
    ∀ i : Fin (binom 4 2), delta (Cochain.zero 4 1) i = false := by decide

/-! ## Δ⁴ (n=5) — 213 atomic -/

theorem dim_n5 :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1 := by decide

theorem delta_zero_preserves_zero_5_2 :
    ∀ i : Fin (binom 5 3), delta (Cochain.zero 5 2) i = false := by decide

theorem delta_zero_preserves_zero_5_3 :
    ∀ i : Fin (binom 5 4), delta (Cochain.zero 5 3) i = false := by decide

/-- ★ capstone — face counts + Hodge dim duality + δ
    preserves zero for the cochain complex on Δ⁴. -/
theorem phase_CA_capstone :
    (binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
     ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1)
    ∧ (binom 5 1 = binom 5 4)
    ∧ (binom 5 2 = binom 5 3)
    ∧ (∀ i : Fin (binom 5 2), delta (Cochain.zero 5 1) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (Cochain.zero 5 2) i = false)
    ∧ (∀ i : Fin (binom 5 4), delta (Cochain.zero 5 3) i = false) := by
  decide

end E213.Math.Cohomology.TrivialCases
