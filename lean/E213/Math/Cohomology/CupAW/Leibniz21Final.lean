import E213.Math.Cohomology.CupAW.Leibniz21Bridge

/-!
# (5, 2, 1) Universal Cup AW Leibniz — closed via two-lens lift
-/

namespace E213.Math.Cohomology.CupAW.Leibniz21Final

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.CupAW.BasisLeibniz (basis basis_leibniz_5_2_1)
open E213.Math.Cohomology.Cochain5_1DecompR (bz5_1)
open E213.Math.Cohomology.Cochain5_2Decomp (bz5_2)
open E213.Math.Cohomology.CupAW.Leibniz22Bridge (cupAW_zero_left_fn
  cupAW_zero_right_fn delta_zero_fn bz5_2_false bz5_2_true)
open E213.Math.Cohomology.CupAW.Leibniz21Bridge (bz5_1_false bz5_1_true)

/-- Per-α-component Leibniz at (bz5_2 α p, basis 5 1 k). -/
theorem h_components_α (α : Cochain 5 2) (k : Fin 5)
    (i : Fin (binom 5 3)) (p : Fin 10) :
    delta (cupAW 5 2 1 (bz5_2 α p) (basis 5 1 k)) i
      = xor (cupAW 5 3 1 (delta (bz5_2 α p)) (basis 5 1 k) i)
            (cupAW 5 2 2 (bz5_2 α p) (delta (basis 5 1 k)) i) := by
  cases hα : α p
  · rw [bz5_2_false α p hα]
    have h1 : cupAW 5 2 1 (Cochain.zero 5 2) (basis 5 1 k)
              = Cochain.zero 5 2 := cupAW_zero_left_fn _ _ _ _
    have h2 : delta (Cochain.zero 5 2) = Cochain.zero 5 3 :=
      delta_zero_fn _ _
    have h3 : cupAW 5 3 1 (Cochain.zero 5 3) (basis 5 1 k)
              = Cochain.zero 5 3 := cupAW_zero_left_fn _ _ _ _
    have h4 : cupAW 5 2 2 (Cochain.zero 5 2) (delta (basis 5 1 k))
              = Cochain.zero 5 3 := cupAW_zero_left_fn _ _ _ _
    rw [h1, h2, h3, h4]
    show false = xor false false
    rfl
  · rw [bz5_2_true α p hα]
    exact basis_leibniz_5_2_1 p k i

/-- ∀ α : Cochain 5 2, Leibniz with β = basis 5 1 k. -/
theorem leibniz_α_basis (α : Cochain 5 2) (k : Fin 5)
    (i : Fin (binom 5 3)) :
    delta (cupAW 5 2 1 α (basis 5 1 k)) i
      = xor (cupAW 5 3 1 (delta α) (basis 5 1 k) i)
            (cupAW 5 2 2 α (delta (basis 5 1 k)) i) :=
  CupAWLeibnizAlgLift21Alpha.leibniz_via_α_decomp_21
    α (basis 5 1 k) i (h_components_α α k i)

/-- Per-β-component Leibniz: cases on β k. -/
theorem h_components_β (α : Cochain 5 2) (β : Cochain 5 1)
    (i : Fin (binom 5 3)) (k : Fin 5) :
    delta (cupAW 5 2 1 α (bz5_1 β k)) i
      = xor (cupAW 5 3 1 (delta α) (bz5_1 β k) i)
            (cupAW 5 2 2 α (delta (bz5_1 β k)) i) := by
  cases hβ : β k
  · rw [bz5_1_false β k hβ]
    have h1 : cupAW 5 2 1 α (Cochain.zero 5 1) = Cochain.zero 5 2 :=
      cupAW_zero_right_fn _ _ _ _
    have h2 : cupAW 5 3 1 (delta α) (Cochain.zero 5 1)
              = Cochain.zero 5 3 := cupAW_zero_right_fn _ _ _ _
    have h3 : delta (Cochain.zero 5 1) = Cochain.zero 5 2 :=
      delta_zero_fn _ _
    have h4 : cupAW 5 2 2 α (Cochain.zero 5 2) = Cochain.zero 5 3 :=
      cupAW_zero_right_fn _ _ _ _
    have h5 : delta (Cochain.zero 5 2) = Cochain.zero 5 3 :=
      delta_zero_fn _ _
    rw [h1, h2, h3, h4, h5]
    show false = xor false false
    rfl
  · rw [bz5_1_true β k hβ]
    exact leibniz_α_basis α k i

/-- ★★★★★ Universal (5,2,1) Cup AW Leibniz — algebraic lift CLOSED. -/
theorem leibniz_universal_5_2_1
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) :=
  CupAWLeibnizAlgLift21.leibniz_via_β_decomp_21
    α β i (h_components_β α β i)

end E213.Math.Cohomology.CupAW.Leibniz21Final
