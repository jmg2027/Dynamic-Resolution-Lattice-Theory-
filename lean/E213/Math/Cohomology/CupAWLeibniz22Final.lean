import E213.Math.Cohomology.CupAWLeibniz22Bridge

/-!
# (5, 2, 2) Universal Cup AW Leibniz — closed via two-lens lift

α : Cochain 5 2, β : Cochain 5 2.  Lift via:
  1. Decompose β (10 components, basis or zero per `β q`)
  2. Per-(α, basis q) Leibniz: decompose α (10 components),
     reduces to (basis p, basis q) basis Leibniz
  3. Each `combine_10` closes the residual XOR rearrangement
-/

namespace E213.Math.Cohomology.CupAWLeibniz22Final

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.CupAWBasisLeibniz (basis basis_leibniz_5_2_2)
open E213.Math.Cohomology.Cochain5_2Decomp (bz5_2)
open E213.Math.Cohomology.CupAWLeibniz22Bridge (bz5_2_false bz5_2_true
  cupAW_zero_left_fn cupAW_zero_right_fn delta_zero_fn)

/-- Per-α-component Leibniz at (bz5_2 α p, basis 5 2 q). -/
theorem h_components_α (α : Cochain 5 2) (q : Fin 10)
    (i : Fin (binom 5 4)) (p : Fin 10) :
    delta (cupAW 5 2 2 (bz5_2 α p) (basis 5 2 q)) i
      = xor (cupAW 5 3 2 (delta (bz5_2 α p)) (basis 5 2 q) i)
            (cupAW 5 2 3 (bz5_2 α p) (delta (basis 5 2 q)) i) := by
  cases hα : α p
  · rw [bz5_2_false α p hα]
    have h1 : cupAW 5 2 2 (Cochain.zero 5 2) (basis 5 2 q)
              = Cochain.zero 5 3 := cupAW_zero_left_fn _ _ _ _
    have h2 : delta (Cochain.zero 5 2) = Cochain.zero 5 3 :=
      delta_zero_fn _ _
    have h3 : cupAW 5 3 2 (Cochain.zero 5 3) (basis 5 2 q)
              = Cochain.zero 5 4 := cupAW_zero_left_fn _ _ _ _
    have h4 : cupAW 5 2 3 (Cochain.zero 5 2) (delta (basis 5 2 q))
              = Cochain.zero 5 4 := cupAW_zero_left_fn _ _ _ _
    rw [h1, h2, h3, h4]
    show delta (Cochain.zero 5 3) i = xor false false
    rw [delta_zero_fn]
    rfl
  · rw [bz5_2_true α p hα]
    exact basis_leibniz_5_2_2 p q i

/-- ∀ α : Cochain 5 2, Leibniz with β = basis 5 2 q. -/
theorem leibniz_α_basis (α : Cochain 5 2) (q : Fin 10)
    (i : Fin (binom 5 4)) :
    delta (cupAW 5 2 2 α (basis 5 2 q)) i
      = xor (cupAW 5 3 2 (delta α) (basis 5 2 q) i)
            (cupAW 5 2 3 α (delta (basis 5 2 q)) i) :=
  CupAWLeibnizAlgLift22Alpha.leibniz_via_α_decomp_22
    α (basis 5 2 q) i (h_components_α α q i)

/-- Per-β-component Leibniz: cases on β q. -/
theorem h_components_β (α β : Cochain 5 2)
    (i : Fin (binom 5 4)) (q : Fin 10) :
    delta (cupAW 5 2 2 α (bz5_2 β q)) i
      = xor (cupAW 5 3 2 (delta α) (bz5_2 β q) i)
            (cupAW 5 2 3 α (delta (bz5_2 β q)) i) := by
  cases hβ : β q
  · rw [bz5_2_false β q hβ]
    have h1 : cupAW 5 2 2 α (Cochain.zero 5 2) = Cochain.zero 5 3 :=
      cupAW_zero_right_fn _ _ _ _
    have h2 : cupAW 5 3 2 (delta α) (Cochain.zero 5 2)
              = Cochain.zero 5 4 := cupAW_zero_right_fn _ _ _ _
    have h3 : delta (Cochain.zero 5 2) = Cochain.zero 5 3 :=
      delta_zero_fn _ _
    have h4 : cupAW 5 2 3 α (Cochain.zero 5 3) = Cochain.zero 5 4 :=
      cupAW_zero_right_fn _ _ _ _
    rw [h1, h2, h3, h4]
    show delta (Cochain.zero 5 3) i = xor false false
    rw [delta_zero_fn]
    rfl
  · rw [bz5_2_true β q hβ]
    exact leibniz_α_basis α q i

/-- ★★★★★ Universal Cup AW Leibniz at (5, 2, 2) — algebraic lift CLOSED. -/
theorem leibniz_universal_5_2_2
    (α β : Cochain 5 2) (i : Fin (binom 5 4)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) :=
  CupAWLeibnizAlgLift22.leibniz_via_β_decomp_22
    α β i (h_components_β α β i)

end E213.Math.Cohomology.CupAWLeibniz22Final
