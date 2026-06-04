import E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulRule

/-!
# Quaternion multiplication table — basis distinctness (∅-axiom)

Hamilton's basis: `1, i, j, k`.  All four are pairwise distinct.

213-native witness: each pair of basis elements differs at some
specific cut-component, witnessed by `decide` at point (0, 1).
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulTable

open E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulRule
  (Quat quatOne quatI quatJ quatK)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- Helper: `(constCut 1 1) ≠ (constCut 0 1)` pointwise at (0,1). -/
theorem cuts_distinct_at_0_1 :
    (constCut 1 1 : Nat → Nat → Bool) 0 1 = false
    ∧ (constCut 0 1 : Nat → Nat → Bool) 0 1 = true :=
  ⟨by decide, by decide⟩

/-- ★ **Basis i ≠ j**: witnessed at first imaginary component. -/
theorem quatI_neq_quatJ : quatI ≠ quatJ := by
  intro h
  have h1 : quatI.1.2 = quatJ.1.2 := by rw [h]
  have hi : quatI.1.2 = constCut 1 1 := rfl
  have hj : quatJ.1.2 = constCut 0 1 := rfl
  rw [hi, hj] at h1
  have hpt : (constCut 1 1 : Nat → Nat → Bool) 0 1
            = (constCut 0 1 : Nat → Nat → Bool) 0 1 := by rw [h1]
  have ⟨e1, e2⟩ := cuts_distinct_at_0_1
  rw [e1, e2] at hpt
  exact Bool.noConfusion hpt

/-- ★ **Basis i ≠ k**: same first-component witness. -/
theorem quatI_neq_quatK : quatI ≠ quatK := by
  intro h
  have h1 : quatI.1.2 = quatK.1.2 := by rw [h]
  have hi : quatI.1.2 = constCut 1 1 := rfl
  have hk : quatK.1.2 = constCut 0 1 := rfl
  rw [hi, hk] at h1
  have hpt : (constCut 1 1 : Nat → Nat → Bool) 0 1
            = (constCut 0 1 : Nat → Nat → Bool) 0 1 := by rw [h1]
  have ⟨e1, e2⟩ := cuts_distinct_at_0_1
  rw [e1, e2] at hpt
  exact Bool.noConfusion hpt

/-- ★ **Basis 1 ≠ i**: identity vs first-imaginary basis. -/
theorem quatOne_neq_quatI : quatOne ≠ quatI := by
  intro h
  have h1 : quatOne.1.1 = quatI.1.1 := by rw [h]
  have hone : quatOne.1.1 = constCut 1 1 := rfl
  have hi : quatI.1.1 = constCut 0 1 := rfl
  rw [hone, hi] at h1
  have hpt : (constCut 1 1 : Nat → Nat → Bool) 0 1
            = (constCut 0 1 : Nat → Nat → Bool) 0 1 := by rw [h1]
  have ⟨e1, e2⟩ := cuts_distinct_at_0_1
  rw [e1, e2] at hpt
  exact Bool.noConfusion hpt

end E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulTable
