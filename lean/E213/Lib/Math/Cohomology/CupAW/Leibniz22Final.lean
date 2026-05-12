import E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.Delta.Pointwise

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# (5, 2, 2) Universal Cup AW Leibniz — closed via two-lens lift

α : Cochain 5 2, β : Cochain 5 2.  Lift via:
  1. Decompose β (10 components, basis or zero per `β q`)
  2. Per-(α, basis q) Leibniz: decompose α (10 components),
     reduces to (basis p, basis q) basis Leibniz
  3. Each `combine_10` closes the residual XOR rearrangement
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz22Final

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis basis_leibniz_5_2_2)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (bz5_2)
open E213.Lib.Math.Cohomology.CupAW.Leibniz22Bridge (bz5_2_false_at bz5_2_true_at)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.CupAW.Zero
  (cupAW_zero_left cupAW_zero_right delta_zero)

/-- Per-α-component Leibniz at (bz5_2 α p, basis 5 2 q).
    PURE — pointwise lifts via cupAW/delta_pointwise_eq, no funext. -/
theorem h_components_α (α : Cochain 5 2) (q : Fin 10)
    (i : Fin (binom 5 4)) (p : Fin 10) :
    delta (cupAW 5 2 2 (bz5_2 α p) (basis 5 2 q)) i
      = xor (cupAW 5 3 2 (delta (bz5_2 α p)) (basis 5 2 q) i)
            (cupAW 5 2 3 (bz5_2 α p) (delta (basis 5 2 q)) i) := by
  cases hα : α p
  · -- α p = false ⟹ bz5_2 α p = 0 pointwise; all three terms collapse.
    have h_bz : ∀ j, bz5_2 α p j = Cochain.zero 5 2 j :=
      bz5_2_false_at α p hα
    have h_delta_bz : ∀ j, delta (bz5_2 α p) j = Cochain.zero 5 3 j :=
      fun j => (delta_pointwise_eq _ _ h_bz j).trans (delta_zero 5 2 j)
    have h_lhs : delta (cupAW 5 2 2 (bz5_2 α p) (basis 5 2 q)) i = false := by
      have h_cup_pw : ∀ j, cupAW 5 2 2 (bz5_2 α p) (basis 5 2 q) j
                         = Cochain.zero 5 3 j := fun j => by
        have step := cupAW_pointwise_eq (bz5_2 α p) (Cochain.zero 5 2)
                       (basis 5 2 q) (basis 5 2 q) h_bz (fun _ => rfl) j
        exact step.trans (cupAW_zero_left 5 2 2 (basis 5 2 q) j)
      exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 3 i)
    have h_rhs1 : cupAW 5 3 2 (delta (bz5_2 α p)) (basis 5 2 q) i = false := by
      have step := cupAW_pointwise_eq (delta (bz5_2 α p)) (Cochain.zero 5 3)
                     (basis 5 2 q) (basis 5 2 q) h_delta_bz (fun _ => rfl) i
      exact step.trans (cupAW_zero_left 5 3 2 (basis 5 2 q) i)
    have h_rhs2 : cupAW 5 2 3 (bz5_2 α p) (delta (basis 5 2 q)) i = false := by
      have step := cupAW_pointwise_eq (bz5_2 α p) (Cochain.zero 5 2)
                     (delta (basis 5 2 q)) (delta (basis 5 2 q))
                     h_bz (fun _ => rfl) i
      exact step.trans (cupAW_zero_left 5 2 3 (delta (basis 5 2 q)) i)
    rw [h_lhs, h_rhs1, h_rhs2]; rfl
  · -- α p = true ⟹ bz5_2 α p = basis 5 2 p pointwise; reduce to basis_leibniz.
    have h_bz : ∀ j, bz5_2 α p j = basis 5 2 p j :=
      bz5_2_true_at α p hα
    have h_delta_bz : ∀ j, delta (bz5_2 α p) j = delta (basis 5 2 p) j :=
      fun j => delta_pointwise_eq _ _ h_bz j
    have h_lhs : delta (cupAW 5 2 2 (bz5_2 α p) (basis 5 2 q)) i
               = delta (cupAW 5 2 2 (basis 5 2 p) (basis 5 2 q)) i := by
      apply delta_pointwise_eq
      intro j
      exact cupAW_pointwise_eq (bz5_2 α p) (basis 5 2 p)
              (basis 5 2 q) (basis 5 2 q) h_bz (fun _ => rfl) j
    have h_rhs1 : cupAW 5 3 2 (delta (bz5_2 α p)) (basis 5 2 q) i
                = cupAW 5 3 2 (delta (basis 5 2 p)) (basis 5 2 q) i :=
      cupAW_pointwise_eq (delta (bz5_2 α p)) (delta (basis 5 2 p))
        (basis 5 2 q) (basis 5 2 q) h_delta_bz (fun _ => rfl) i
    have h_rhs2 : cupAW 5 2 3 (bz5_2 α p) (delta (basis 5 2 q)) i
                = cupAW 5 2 3 (basis 5 2 p) (delta (basis 5 2 q)) i :=
      cupAW_pointwise_eq (bz5_2 α p) (basis 5 2 p)
        (delta (basis 5 2 q)) (delta (basis 5 2 q)) h_bz (fun _ => rfl) i
    rw [h_lhs, h_rhs1, h_rhs2]
    exact basis_leibniz_5_2_2 p q i

/-- ∀ α : Cochain 5 2, Leibniz with β = basis 5 2 q. -/
theorem leibniz_α_basis (α : Cochain 5 2) (q : Fin 10)
    (i : Fin (binom 5 4)) :
    delta (cupAW 5 2 2 α (basis 5 2 q)) i
      = xor (cupAW 5 3 2 (delta α) (basis 5 2 q) i)
            (cupAW 5 2 3 α (delta (basis 5 2 q)) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22
    α (basis 5 2 q) i (h_components_α α q i)

/-- Per-β-component Leibniz: cases on β q.  PURE — same pointwise template. -/
theorem h_components_β (α β : Cochain 5 2)
    (i : Fin (binom 5 4)) (q : Fin 10) :
    delta (cupAW 5 2 2 α (bz5_2 β q)) i
      = xor (cupAW 5 3 2 (delta α) (bz5_2 β q) i)
            (cupAW 5 2 3 α (delta (bz5_2 β q)) i) := by
  cases hβ : β q
  · have h_bz : ∀ j, bz5_2 β q j = Cochain.zero 5 2 j :=
      bz5_2_false_at β q hβ
    have h_delta_bz : ∀ j, delta (bz5_2 β q) j = Cochain.zero 5 3 j :=
      fun j => (delta_pointwise_eq _ _ h_bz j).trans (delta_zero 5 2 j)
    have h_lhs : delta (cupAW 5 2 2 α (bz5_2 β q)) i = false := by
      have h_cup_pw : ∀ j, cupAW 5 2 2 α (bz5_2 β q) j
                         = Cochain.zero 5 3 j := fun j => by
        have step := cupAW_pointwise_eq α α (bz5_2 β q) (Cochain.zero 5 2)
                       (fun _ => rfl) h_bz j
        exact step.trans (cupAW_zero_right 5 2 2 α j)
      exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 3 i)
    have h_rhs1 : cupAW 5 3 2 (delta α) (bz5_2 β q) i = false := by
      have step := cupAW_pointwise_eq (delta α) (delta α)
                     (bz5_2 β q) (Cochain.zero 5 2) (fun _ => rfl) h_bz i
      exact step.trans (cupAW_zero_right 5 3 2 (delta α) i)
    have h_rhs2 : cupAW 5 2 3 α (delta (bz5_2 β q)) i = false := by
      have step := cupAW_pointwise_eq α α (delta (bz5_2 β q)) (Cochain.zero 5 3)
                     (fun _ => rfl) h_delta_bz i
      exact step.trans (cupAW_zero_right 5 2 3 α i)
    rw [h_lhs, h_rhs1, h_rhs2]; rfl
  · have h_bz : ∀ j, bz5_2 β q j = basis 5 2 q j :=
      bz5_2_true_at β q hβ
    have h_delta_bz : ∀ j, delta (bz5_2 β q) j = delta (basis 5 2 q) j :=
      fun j => delta_pointwise_eq _ _ h_bz j
    have h_lhs : delta (cupAW 5 2 2 α (bz5_2 β q)) i
               = delta (cupAW 5 2 2 α (basis 5 2 q)) i := by
      apply delta_pointwise_eq
      intro j
      exact cupAW_pointwise_eq α α (bz5_2 β q) (basis 5 2 q)
              (fun _ => rfl) h_bz j
    have h_rhs1 : cupAW 5 3 2 (delta α) (bz5_2 β q) i
                = cupAW 5 3 2 (delta α) (basis 5 2 q) i :=
      cupAW_pointwise_eq (delta α) (delta α) (bz5_2 β q) (basis 5 2 q)
        (fun _ => rfl) h_bz i
    have h_rhs2 : cupAW 5 2 3 α (delta (bz5_2 β q)) i
                = cupAW 5 2 3 α (delta (basis 5 2 q)) i :=
      cupAW_pointwise_eq α α (delta (bz5_2 β q)) (delta (basis 5 2 q))
        (fun _ => rfl) h_delta_bz i
    rw [h_lhs, h_rhs1, h_rhs2]
    exact leibniz_α_basis α q i

/-- ★★★★★ Universal Cup AW Leibniz at (5, 2, 2) — algebraic lift CLOSED. -/
theorem leibniz_universal_5_2_2
    (α β : Cochain 5 2) (i : Fin (binom 5 4)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) :=
  E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22.leibniz_via_β_decomp_22
    α β i (h_components_β α β i)

end E213.Lib.Math.Cohomology.CupAW.Leibniz22Final
