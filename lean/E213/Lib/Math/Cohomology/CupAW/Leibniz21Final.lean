import E213.Lib.Math.Cohomology.CupAW.Leibniz21Bridge
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.Delta.Pointwise

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# (5, 2, 1) Universal Cup AW Leibniz — closed via two-lens lift
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz21Final

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis basis_leibniz_5_2_1)
open E213.Lib.Math.Cohomology.Cochain.V5_1DecompR (bz5_1)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge (bz5_2_false_at bz5_2_true_at)
open E213.Lib.Math.Cohomology.CupAW.Leibniz21Bridge (bz5_1_false_at bz5_1_true_at)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.CupAW.Zero
  (cupAW_zero_left cupAW_zero_right delta_zero)

/-- Per-α-component Leibniz at (bz5_2 α p, basis 5 1 k).  PURE. -/
theorem h_components_α (α : Cochain 5 2) (k : Fin 5)
    (i : Fin (binom 5 3)) (p : Fin 10) :
    delta (cupAW 5 2 1 (bz5_2 α p) (basis 5 1 k)) i
      = xor (cupAW 5 3 1 (delta (bz5_2 α p)) (basis 5 1 k) i)
            (cupAW 5 2 2 (bz5_2 α p) (delta (basis 5 1 k)) i) := by
  cases hα : α p
  · have h_bz : ∀ j, bz5_2 α p j = Cochain.zero 5 2 j :=
      bz5_2_false_at α p hα
    have h_delta_bz : ∀ j, delta (bz5_2 α p) j = Cochain.zero 5 3 j :=
      fun j => (delta_pointwise_eq _ _ h_bz j).trans (delta_zero 5 2 j)
    have h_lhs : delta (cupAW 5 2 1 (bz5_2 α p) (basis 5 1 k)) i = false := by
      have h_cup_pw : ∀ j, cupAW 5 2 1 (bz5_2 α p) (basis 5 1 k) j
                         = Cochain.zero 5 2 j := fun j => by
        have step := cupAW_pointwise_eq (bz5_2 α p) (Cochain.zero 5 2)
                       (basis 5 1 k) (basis 5 1 k) h_bz (fun _ => rfl) j
        exact step.trans (cupAW_zero_left 5 2 1 (basis 5 1 k) j)
      exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 2 i)
    have h_rhs1 : cupAW 5 3 1 (delta (bz5_2 α p)) (basis 5 1 k) i = false := by
      have step := cupAW_pointwise_eq (delta (bz5_2 α p)) (Cochain.zero 5 3)
                     (basis 5 1 k) (basis 5 1 k) h_delta_bz (fun _ => rfl) i
      exact step.trans (cupAW_zero_left 5 3 1 (basis 5 1 k) i)
    have h_rhs2 : cupAW 5 2 2 (bz5_2 α p) (delta (basis 5 1 k)) i = false := by
      have step := cupAW_pointwise_eq (bz5_2 α p) (Cochain.zero 5 2)
                     (delta (basis 5 1 k)) (delta (basis 5 1 k))
                     h_bz (fun _ => rfl) i
      exact step.trans (cupAW_zero_left 5 2 2 (delta (basis 5 1 k)) i)
    rw [h_lhs, h_rhs1, h_rhs2]; rfl
  · have h_bz : ∀ j, bz5_2 α p j = basis 5 2 p j :=
      bz5_2_true_at α p hα
    have h_delta_bz : ∀ j, delta (bz5_2 α p) j = delta (basis 5 2 p) j :=
      fun j => delta_pointwise_eq _ _ h_bz j
    have h_lhs : delta (cupAW 5 2 1 (bz5_2 α p) (basis 5 1 k)) i
               = delta (cupAW 5 2 1 (basis 5 2 p) (basis 5 1 k)) i := by
      apply delta_pointwise_eq
      intro j
      exact cupAW_pointwise_eq (bz5_2 α p) (basis 5 2 p)
              (basis 5 1 k) (basis 5 1 k) h_bz (fun _ => rfl) j
    have h_rhs1 : cupAW 5 3 1 (delta (bz5_2 α p)) (basis 5 1 k) i
                = cupAW 5 3 1 (delta (basis 5 2 p)) (basis 5 1 k) i :=
      cupAW_pointwise_eq (delta (bz5_2 α p)) (delta (basis 5 2 p))
        (basis 5 1 k) (basis 5 1 k) h_delta_bz (fun _ => rfl) i
    have h_rhs2 : cupAW 5 2 2 (bz5_2 α p) (delta (basis 5 1 k)) i
                = cupAW 5 2 2 (basis 5 2 p) (delta (basis 5 1 k)) i :=
      cupAW_pointwise_eq (bz5_2 α p) (basis 5 2 p)
        (delta (basis 5 1 k)) (delta (basis 5 1 k)) h_bz (fun _ => rfl) i
    rw [h_lhs, h_rhs1, h_rhs2]
    exact basis_leibniz_5_2_1 p k i

/-- ∀ α : Cochain 5 2, Leibniz with β = basis 5 1 k. -/
theorem leibniz_α_basis (α : Cochain 5 2) (k : Fin 5)
    (i : Fin (binom 5 3)) :
    delta (cupAW 5 2 1 α (basis 5 1 k)) i
      = xor (cupAW 5 3 1 (delta α) (basis 5 1 k) i)
            (cupAW 5 2 2 α (delta (basis 5 1 k)) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21
    α (basis 5 1 k) i (h_components_α α k i)

/-- Per-β-component Leibniz: cases on β k.  PURE. -/
theorem h_components_β (α : Cochain 5 2) (β : Cochain 5 1)
    (i : Fin (binom 5 3)) (k : Fin 5) :
    delta (cupAW 5 2 1 α (bz5_1 β k)) i
      = xor (cupAW 5 3 1 (delta α) (bz5_1 β k) i)
            (cupAW 5 2 2 α (delta (bz5_1 β k)) i) := by
  cases hβ : β k
  · have h_bz : ∀ j, bz5_1 β k j = Cochain.zero 5 1 j :=
      bz5_1_false_at β k hβ
    have h_delta_bz : ∀ j, delta (bz5_1 β k) j = Cochain.zero 5 2 j :=
      fun j => (delta_pointwise_eq _ _ h_bz j).trans (delta_zero 5 1 j)
    have h_lhs : delta (cupAW 5 2 1 α (bz5_1 β k)) i = false := by
      have h_cup_pw : ∀ j, cupAW 5 2 1 α (bz5_1 β k) j
                         = Cochain.zero 5 2 j := fun j => by
        have step := cupAW_pointwise_eq α α (bz5_1 β k) (Cochain.zero 5 1)
                       (fun _ => rfl) h_bz j
        exact step.trans (cupAW_zero_right 5 2 1 α j)
      exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 2 i)
    have h_rhs1 : cupAW 5 3 1 (delta α) (bz5_1 β k) i = false := by
      have step := cupAW_pointwise_eq (delta α) (delta α)
                     (bz5_1 β k) (Cochain.zero 5 1) (fun _ => rfl) h_bz i
      exact step.trans (cupAW_zero_right 5 3 1 (delta α) i)
    have h_rhs2 : cupAW 5 2 2 α (delta (bz5_1 β k)) i = false := by
      have step := cupAW_pointwise_eq α α (delta (bz5_1 β k)) (Cochain.zero 5 2)
                     (fun _ => rfl) h_delta_bz i
      exact step.trans (cupAW_zero_right 5 2 2 α i)
    rw [h_lhs, h_rhs1, h_rhs2]; rfl
  · have h_bz : ∀ j, bz5_1 β k j = basis 5 1 k j :=
      bz5_1_true_at β k hβ
    have h_delta_bz : ∀ j, delta (bz5_1 β k) j = delta (basis 5 1 k) j :=
      fun j => delta_pointwise_eq _ _ h_bz j
    have h_lhs : delta (cupAW 5 2 1 α (bz5_1 β k)) i
               = delta (cupAW 5 2 1 α (basis 5 1 k)) i := by
      apply delta_pointwise_eq
      intro j
      exact cupAW_pointwise_eq α α (bz5_1 β k) (basis 5 1 k)
              (fun _ => rfl) h_bz j
    have h_rhs1 : cupAW 5 3 1 (delta α) (bz5_1 β k) i
                = cupAW 5 3 1 (delta α) (basis 5 1 k) i :=
      cupAW_pointwise_eq (delta α) (delta α) (bz5_1 β k) (basis 5 1 k)
        (fun _ => rfl) h_bz i
    have h_rhs2 : cupAW 5 2 2 α (delta (bz5_1 β k)) i
                = cupAW 5 2 2 α (delta (basis 5 1 k)) i :=
      cupAW_pointwise_eq α α (delta (bz5_1 β k)) (delta (basis 5 1 k))
        (fun _ => rfl) h_delta_bz i
    rw [h_lhs, h_rhs1, h_rhs2]
    exact leibniz_α_basis α k i

/-- ★★★★★ Universal (5,2,1) Cup AW Leibniz — algebraic lift CLOSED. -/
theorem leibniz_universal_5_2_1
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21.leibniz_via_β_decomp_21
    α β i (h_components_β α β i)

end E213.Lib.Math.Cohomology.CupAW.Leibniz21Final
