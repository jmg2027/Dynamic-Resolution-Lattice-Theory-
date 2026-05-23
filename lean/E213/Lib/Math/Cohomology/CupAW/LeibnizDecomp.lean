import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Physics.Simplex.Counts
/-!
# Leibniz-via-decomposition — parametric helpers (Cochain 5 2 left factor)

Consolidation per  L2.

A common pattern in the (5, 2, 1) and (5, 2, 2) Cup-AW Leibniz lifts:
a basis-component family `bz5_X β k j` either collapses to
`Cochain.zero 5 _ j` (when `β k = false`) or coincides with
`basis 5 _ k j` (when `β k = true`).  In the false case the Leibniz
identity collapses to `false = xor false false` via the
`cupAW_zero_left`/`cupAW_zero_right` + `delta_zero` package; in the
true case it reduces to the basis Leibniz at the basis term.

Two parametric helpers per side, specialised to the two right-degree
cases `b ∈ {1, 2}` actually used in `Leibniz{21,22}Final.lean`.  This
keeps Nat arithmetic in the `Fin (binom 5 _)` indices definitionally
reducible (`2 + b - 1 + 1` does not reduce for abstract `b`).
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.CupAW.Zero
  (cupAW_zero_left cupAW_zero_right delta_zero)

/-! ### Right-degree 1 (used by Leibniz21Final) -/

/-- Zero-collapse on the LEFT factor at (5, 2, 1).  PURE. -/
theorem leibniz_zero_collapse_left_5_2_1
    (γ : Cochain 5 2) (β : Cochain 5 1)
    (i : Fin (binom 5 3))
    (h : ∀ j, γ j = Cochain.zero 5 2 j) :
    delta (cupAW 5 2 1 γ β) i
      = xor (cupAW 5 3 1 (delta γ) β i)
            (cupAW 5 2 2 γ (delta β) i) := by
  have h_delta_γ : ∀ j, delta γ j = Cochain.zero 5 3 j :=
    fun j => (delta_pointwise_eq _ _ h j).trans (delta_zero 5 2 j)
  have h_lhs : delta (cupAW 5 2 1 γ β) i = false := by
    have h_cup_pw : ∀ j, cupAW 5 2 1 γ β j = Cochain.zero 5 2 j := fun j => by
      have step := cupAW_pointwise_eq γ (Cochain.zero 5 2) β β h (fun _ => rfl) j
      exact step.trans (cupAW_zero_left 5 2 1 β j)
    exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 2 i)
  have h_rhs1 : cupAW 5 3 1 (delta γ) β i = false := by
    have step := cupAW_pointwise_eq (delta γ) (Cochain.zero 5 3) β β
                   h_delta_γ (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 3 1 β i)
  have h_rhs2 : cupAW 5 2 2 γ (delta β) i = false := by
    have step := cupAW_pointwise_eq γ (Cochain.zero 5 2) (delta β) (delta β)
                   h (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 2 2 (delta β) i)
  rw [h_lhs, h_rhs1, h_rhs2]; rfl

/-- Pointwise transport on the LEFT factor at (5, 2, 1).  PURE. -/
theorem leibniz_pointwise_transport_left_5_2_1
    (γ γ' : Cochain 5 2) (β : Cochain 5 1)
    (i : Fin (binom 5 3))
    (h : ∀ j, γ j = γ' j)
    (basis_leib : delta (cupAW 5 2 1 γ' β) i
                = xor (cupAW 5 3 1 (delta γ') β i)
                      (cupAW 5 2 2 γ' (delta β) i)) :
    delta (cupAW 5 2 1 γ β) i
      = xor (cupAW 5 3 1 (delta γ) β i)
            (cupAW 5 2 2 γ (delta β) i) := by
  have h_delta : ∀ j, delta γ j = delta γ' j :=
    fun j => delta_pointwise_eq _ _ h j
  have h_lhs : delta (cupAW 5 2 1 γ β) i = delta (cupAW 5 2 1 γ' β) i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq γ γ' β β h (fun _ => rfl) j
  have h_rhs1 : cupAW 5 3 1 (delta γ) β i = cupAW 5 3 1 (delta γ') β i :=
    cupAW_pointwise_eq (delta γ) (delta γ') β β h_delta (fun _ => rfl) i
  have h_rhs2 : cupAW 5 2 2 γ (delta β) i = cupAW 5 2 2 γ' (delta β) i :=
    cupAW_pointwise_eq γ γ' (delta β) (delta β) h (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  exact basis_leib

/-- Zero-collapse on the RIGHT factor at (5, 2, 1).  PURE. -/
theorem leibniz_zero_collapse_right_5_2_1
    (α : Cochain 5 2) (γ : Cochain 5 1)
    (i : Fin (binom 5 3))
    (h : ∀ j, γ j = Cochain.zero 5 1 j) :
    delta (cupAW 5 2 1 α γ) i
      = xor (cupAW 5 3 1 (delta α) γ i)
            (cupAW 5 2 2 α (delta γ) i) := by
  have h_delta_γ : ∀ j, delta γ j = Cochain.zero 5 2 j :=
    fun j => (delta_pointwise_eq _ _ h j).trans (delta_zero 5 1 j)
  have h_lhs : delta (cupAW 5 2 1 α γ) i = false := by
    have h_cup_pw : ∀ j, cupAW 5 2 1 α γ j = Cochain.zero 5 2 j := fun j => by
      have step := cupAW_pointwise_eq α α γ (Cochain.zero 5 1) (fun _ => rfl) h j
      exact step.trans (cupAW_zero_right 5 2 1 α j)
    exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 2 i)
  have h_rhs1 : cupAW 5 3 1 (delta α) γ i = false := by
    have step := cupAW_pointwise_eq (delta α) (delta α) γ (Cochain.zero 5 1)
                   (fun _ => rfl) h i
    exact step.trans (cupAW_zero_right 5 3 1 (delta α) i)
  have h_rhs2 : cupAW 5 2 2 α (delta γ) i = false := by
    have step := cupAW_pointwise_eq α α (delta γ) (Cochain.zero 5 2)
                   (fun _ => rfl) h_delta_γ i
    exact step.trans (cupAW_zero_right 5 2 2 α i)
  rw [h_lhs, h_rhs1, h_rhs2]; rfl

/-- Pointwise transport on the RIGHT factor at (5, 2, 1).  PURE. -/
theorem leibniz_pointwise_transport_right_5_2_1
    (α : Cochain 5 2) (γ γ' : Cochain 5 1)
    (i : Fin (binom 5 3))
    (h : ∀ j, γ j = γ' j)
    (basis_leib : delta (cupAW 5 2 1 α γ') i
                = xor (cupAW 5 3 1 (delta α) γ' i)
                      (cupAW 5 2 2 α (delta γ') i)) :
    delta (cupAW 5 2 1 α γ) i
      = xor (cupAW 5 3 1 (delta α) γ i)
            (cupAW 5 2 2 α (delta γ) i) := by
  have h_delta : ∀ j, delta γ j = delta γ' j :=
    fun j => delta_pointwise_eq _ _ h j
  have h_lhs : delta (cupAW 5 2 1 α γ) i = delta (cupAW 5 2 1 α γ') i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq α α γ γ' (fun _ => rfl) h j
  have h_rhs1 : cupAW 5 3 1 (delta α) γ i = cupAW 5 3 1 (delta α) γ' i :=
    cupAW_pointwise_eq (delta α) (delta α) γ γ' (fun _ => rfl) h i
  have h_rhs2 : cupAW 5 2 2 α (delta γ) i = cupAW 5 2 2 α (delta γ') i :=
    cupAW_pointwise_eq α α (delta γ) (delta γ') (fun _ => rfl) h_delta i
  rw [h_lhs, h_rhs1, h_rhs2]
  exact basis_leib

/-! ### Right-degree 2 (used by Leibniz22Final) -/

/-- Zero-collapse on the LEFT factor at (5, 2, 2).  PURE. -/
theorem leibniz_zero_collapse_left_5_2_2
    (γ : Cochain 5 2) (β : Cochain 5 2)
    (i : Fin (binom 5 4))
    (h : ∀ j, γ j = Cochain.zero 5 2 j) :
    delta (cupAW 5 2 2 γ β) i
      = xor (cupAW 5 3 2 (delta γ) β i)
            (cupAW 5 2 3 γ (delta β) i) := by
  have h_delta_γ : ∀ j, delta γ j = Cochain.zero 5 3 j :=
    fun j => (delta_pointwise_eq _ _ h j).trans (delta_zero 5 2 j)
  have h_lhs : delta (cupAW 5 2 2 γ β) i = false := by
    have h_cup_pw : ∀ j, cupAW 5 2 2 γ β j = Cochain.zero 5 3 j := fun j => by
      have step := cupAW_pointwise_eq γ (Cochain.zero 5 2) β β h (fun _ => rfl) j
      exact step.trans (cupAW_zero_left 5 2 2 β j)
    exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 3 i)
  have h_rhs1 : cupAW 5 3 2 (delta γ) β i = false := by
    have step := cupAW_pointwise_eq (delta γ) (Cochain.zero 5 3) β β
                   h_delta_γ (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 3 2 β i)
  have h_rhs2 : cupAW 5 2 3 γ (delta β) i = false := by
    have step := cupAW_pointwise_eq γ (Cochain.zero 5 2) (delta β) (delta β)
                   h (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 2 3 (delta β) i)
  rw [h_lhs, h_rhs1, h_rhs2]; rfl

/-- Pointwise transport on the LEFT factor at (5, 2, 2).  PURE. -/
theorem leibniz_pointwise_transport_left_5_2_2
    (γ γ' : Cochain 5 2) (β : Cochain 5 2)
    (i : Fin (binom 5 4))
    (h : ∀ j, γ j = γ' j)
    (basis_leib : delta (cupAW 5 2 2 γ' β) i
                = xor (cupAW 5 3 2 (delta γ') β i)
                      (cupAW 5 2 3 γ' (delta β) i)) :
    delta (cupAW 5 2 2 γ β) i
      = xor (cupAW 5 3 2 (delta γ) β i)
            (cupAW 5 2 3 γ (delta β) i) := by
  have h_delta : ∀ j, delta γ j = delta γ' j :=
    fun j => delta_pointwise_eq _ _ h j
  have h_lhs : delta (cupAW 5 2 2 γ β) i = delta (cupAW 5 2 2 γ' β) i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq γ γ' β β h (fun _ => rfl) j
  have h_rhs1 : cupAW 5 3 2 (delta γ) β i = cupAW 5 3 2 (delta γ') β i :=
    cupAW_pointwise_eq (delta γ) (delta γ') β β h_delta (fun _ => rfl) i
  have h_rhs2 : cupAW 5 2 3 γ (delta β) i = cupAW 5 2 3 γ' (delta β) i :=
    cupAW_pointwise_eq γ γ' (delta β) (delta β) h (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  exact basis_leib

/-- Zero-collapse on the RIGHT factor at (5, 2, 2).  PURE. -/
theorem leibniz_zero_collapse_right_5_2_2
    (α : Cochain 5 2) (γ : Cochain 5 2)
    (i : Fin (binom 5 4))
    (h : ∀ j, γ j = Cochain.zero 5 2 j) :
    delta (cupAW 5 2 2 α γ) i
      = xor (cupAW 5 3 2 (delta α) γ i)
            (cupAW 5 2 3 α (delta γ) i) := by
  have h_delta_γ : ∀ j, delta γ j = Cochain.zero 5 3 j :=
    fun j => (delta_pointwise_eq _ _ h j).trans (delta_zero 5 2 j)
  have h_lhs : delta (cupAW 5 2 2 α γ) i = false := by
    have h_cup_pw : ∀ j, cupAW 5 2 2 α γ j = Cochain.zero 5 3 j := fun j => by
      have step := cupAW_pointwise_eq α α γ (Cochain.zero 5 2) (fun _ => rfl) h j
      exact step.trans (cupAW_zero_right 5 2 2 α j)
    exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 3 i)
  have h_rhs1 : cupAW 5 3 2 (delta α) γ i = false := by
    have step := cupAW_pointwise_eq (delta α) (delta α) γ (Cochain.zero 5 2)
                   (fun _ => rfl) h i
    exact step.trans (cupAW_zero_right 5 3 2 (delta α) i)
  have h_rhs2 : cupAW 5 2 3 α (delta γ) i = false := by
    have step := cupAW_pointwise_eq α α (delta γ) (Cochain.zero 5 3)
                   (fun _ => rfl) h_delta_γ i
    exact step.trans (cupAW_zero_right 5 2 3 α i)
  rw [h_lhs, h_rhs1, h_rhs2]; rfl

/-- Pointwise transport on the RIGHT factor at (5, 2, 2).  PURE. -/
theorem leibniz_pointwise_transport_right_5_2_2
    (α : Cochain 5 2) (γ γ' : Cochain 5 2)
    (i : Fin (binom 5 4))
    (h : ∀ j, γ j = γ' j)
    (basis_leib : delta (cupAW 5 2 2 α γ') i
                = xor (cupAW 5 3 2 (delta α) γ' i)
                      (cupAW 5 2 3 α (delta γ') i)) :
    delta (cupAW 5 2 2 α γ) i
      = xor (cupAW 5 3 2 (delta α) γ i)
            (cupAW 5 2 3 α (delta γ) i) := by
  have h_delta : ∀ j, delta γ j = delta γ' j :=
    fun j => delta_pointwise_eq _ _ h j
  have h_lhs : delta (cupAW 5 2 2 α γ) i = delta (cupAW 5 2 2 α γ') i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq α α γ γ' (fun _ => rfl) h j
  have h_rhs1 : cupAW 5 3 2 (delta α) γ i = cupAW 5 3 2 (delta α) γ' i :=
    cupAW_pointwise_eq (delta α) (delta α) γ γ' (fun _ => rfl) h i
  have h_rhs2 : cupAW 5 2 3 α (delta γ) i = cupAW 5 2 3 α (delta γ') i :=
    cupAW_pointwise_eq α α (delta γ) (delta γ') (fun _ => rfl) h_delta i
  rw [h_lhs, h_rhs1, h_rhs2]
  exact basis_leib

end E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp
