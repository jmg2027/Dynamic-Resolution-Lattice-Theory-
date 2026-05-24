import E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1_BasisDecomp
import E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1Bridge
import E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Cochain.V5_3Decomp
import E213.Lib.Math.Cohomology.Universal.Prop51
import E213.Lib.Math.Cohomology.Bridge.XorPairCombine
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW Leibniz at (5, 3, 1) — universal lift via bilinearity

α-side decomposition over 10 basis components (V5_3Decomp),
β-side pattern over 5 Bool components (Prop51).  Same template
as (5, 1, b) family; sister at the codim-3 α stratum.

Bidegree signature: (n, a, b) = (5, 3, 1).
- α : Cochain 5 3 (binom 5 3 = 10 components)
- β : Cochain 5 1 (binom 5 1 = 5 components)
- output : Cochain 5 3 → δ → Cochain 5 4 (Fin 5)

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.V5_3Decomp
  (decomp_5_3 bz5_3
   decomp_step_at_0 decomp_step_at_1 decomp_step_at_2
   decomp_step_at_3 decomp_step_at_4 decomp_step_at_5
   decomp_step_at_6 decomp_step_at_7 decomp_step_at_8
   decomp_step_at_9)
open E213.Lib.Math.Cohomology.Bridge.XorPairCombine (combine_10)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.CupAW.Zero
  (cupAW_zero_left cupAW_zero_right delta_zero)
open E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
  (delta_cupAW_add_left cupAW_delta_add_left)
open E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1Bridge
  (bz5_3_false_at bz5_3_true_at)
open E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1_BasisDecomp
  (leibniz_basis_5_3_1_at_0 leibniz_basis_5_3_1_at_1
   leibniz_basis_5_3_1_at_2 leibniz_basis_5_3_1_at_3
   leibniz_basis_5_3_1_at_4 leibniz_basis_5_3_1_at_5
   leibniz_basis_5_3_1_at_6 leibniz_basis_5_3_1_at_7
   leibniz_basis_5_3_1_at_8 leibniz_basis_5_3_1_at_9)
open E213.Lib.Math.Cohomology.Universal.Prop51 renaming pattern → patternE
open E213.Tactic.NatHelper (cases_lt_ten cases_lt_five)

/-! ## §1 — Zero-collapse + pointwise-transport at (5, 3, 1) -/

private theorem leibniz_zero_collapse_left
    (γ : Cochain 5 3) (β : Cochain 5 1)
    (i : Fin (binom 5 4))
    (h : ∀ j, γ j = Cochain.zero 5 3 j) :
    delta (cupAW 5 3 1 γ β) i
      = xor (cupAW 5 4 1 (delta γ) β i)
            (cupAW 5 3 2 γ (delta β) i) := by
  have h_delta_γ : ∀ j, delta γ j = Cochain.zero 5 4 j :=
    fun j => (delta_pointwise_eq _ _ h j).trans (delta_zero 5 3 j)
  have h_lhs : delta (cupAW 5 3 1 γ β) i = false := by
    have h_cup_pw : ∀ j, cupAW 5 3 1 γ β j = Cochain.zero 5 3 j := fun j => by
      have step :=
        cupAW_pointwise_eq γ (Cochain.zero 5 3) β β h (fun _ => rfl) j
      exact step.trans (cupAW_zero_left 5 3 1 β j)
    exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 3 i)
  have h_rhs1 : cupAW 5 4 1 (delta γ) β i = false := by
    have step :=
      cupAW_pointwise_eq (delta γ) (Cochain.zero 5 4) β β
        h_delta_γ (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 4 1 β i)
  have h_rhs2 : cupAW 5 3 2 γ (delta β) i = false := by
    have step :=
      cupAW_pointwise_eq γ (Cochain.zero 5 3) (delta β) (delta β)
        h (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 3 2 (delta β) i)
  rw [h_lhs, h_rhs1, h_rhs2]; rfl

private theorem leibniz_pointwise_transport_left
    (γ γ' : Cochain 5 3) (β : Cochain 5 1)
    (i : Fin (binom 5 4))
    (h : ∀ j, γ j = γ' j)
    (basis_leib : delta (cupAW 5 3 1 γ' β) i
                = xor (cupAW 5 4 1 (delta γ') β i)
                      (cupAW 5 3 2 γ' (delta β) i)) :
    delta (cupAW 5 3 1 γ β) i
      = xor (cupAW 5 4 1 (delta γ) β i)
            (cupAW 5 3 2 γ (delta β) i) := by
  have h_delta : ∀ j, delta γ j = delta γ' j :=
    fun j => delta_pointwise_eq _ _ h j
  have h_lhs : delta (cupAW 5 3 1 γ β) i = delta (cupAW 5 3 1 γ' β) i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq γ γ' β β h (fun _ => rfl) j
  have h_rhs1 : cupAW 5 4 1 (delta γ) β i = cupAW 5 4 1 (delta γ') β i :=
    cupAW_pointwise_eq (delta γ) (delta γ') β β h_delta (fun _ => rfl) i
  have h_rhs2 : cupAW 5 3 2 γ (delta β) i = cupAW 5 3 2 γ' (delta β) i :=
    cupAW_pointwise_eq γ γ' (delta β) (delta β) h (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  exact basis_leib

/-! ## §2 — Per-basis universal-β lift (10 cases) -/

private theorem leibniz_basis_universal (k : Fin 10)
    (β : Cochain 5 1) (i : Fin (binom 5 4)) :
    delta (cupAW 5 3 1 (basis 5 3 k) β) i
      = xor (cupAW 5 4 1 (delta (basis 5 3 k)) β i)
            (cupAW 5 3 2 (basis 5 3 k) (delta β) i) := by
  let pβ := patternE (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                     (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                     (β ⟨4, by decide⟩)
  rcases k with ⟨n, hn⟩
  rcases (cases_lt_ten hn) with rfl | rfl | rfl | rfl | rfl
                              | rfl | rfl | rfl | rfl | rfl
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨0, by decide⟩) β
      (basis 5 3 ⟨0, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_0
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨1, by decide⟩) β
      (basis 5 3 ⟨1, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_1
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨2, by decide⟩) β
      (basis 5 3 ⟨2, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_2
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨3, by decide⟩) β
      (basis 5 3 ⟨3, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_3
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨4, by decide⟩) β
      (basis 5 3 ⟨4, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_4
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨5, by decide⟩) β
      (basis 5 3 ⟨5, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_5
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨6, by decide⟩) β
      (basis 5 3 ⟨6, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_6
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨7, by decide⟩) β
      (basis 5 3 ⟨7, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_7
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨8, by decide⟩) β
      (basis 5 3 ⟨8, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_8
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 3 1 (basis 5 3 ⟨9, by decide⟩) β
      (basis 5 3 ⟨9, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β)
      (leibniz_basis_5_3_1_at_9
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i)

/-! ## §3 — Per-bz5_3-component Leibniz via case-split -/

private theorem h_components_α (α : Cochain 5 3) (β : Cochain 5 1)
    (i : Fin (binom 5 4)) (k : Fin 10) :
    delta (cupAW 5 3 1 (bz5_3 α k) β) i
      = xor (cupAW 5 4 1 (delta (bz5_3 α k)) β i)
            (cupAW 5 3 2 (bz5_3 α k) (delta β) i) := by
  cases hα : α k
  · exact leibniz_zero_collapse_left
      (bz5_3 α k) β i (bz5_3_false_at α k hα)
  · exact leibniz_pointwise_transport_left
      (bz5_3 α k) (basis 5 3 k) β i (bz5_3_true_at α k hα)
      (leibniz_basis_universal k β i)

/-! ## §4 — α-decomp lens + universal theorem -/

private theorem leibniz_via_α_decomp
    (α : Cochain 5 3) (β : Cochain 5 1) (i : Fin (binom 5 4))
    (h_components : ∀ k : Fin 10,
      delta (cupAW 5 3 1 (bz5_3 α k) β) i
        = xor (cupAW 5 4 1 (delta (bz5_3 α k)) β i)
              (cupAW 5 3 2 (bz5_3 α k) (delta β) i)) :
    delta (cupAW 5 3 1 α β) i
      = xor (cupAW 5 4 1 (delta α) β i)
            (cupAW 5 3 2 α (delta β) i) := by
  have h_α_pw : ∀ j, α j = decomp_5_3 α j := by
    intro j; rcases j with ⟨n, hn⟩
    rcases (cases_lt_ten hn) with rfl | rfl | rfl | rfl | rfl
                                | rfl | rfl | rfl | rfl | rfl
    · exact (decomp_step_at_0 α).symm
    · exact (decomp_step_at_1 α).symm
    · exact (decomp_step_at_2 α).symm
    · exact (decomp_step_at_3 α).symm
    · exact (decomp_step_at_4 α).symm
    · exact (decomp_step_at_5 α).symm
    · exact (decomp_step_at_6 α).symm
    · exact (decomp_step_at_7 α).symm
    · exact (decomp_step_at_8 α).symm
    · exact (decomp_step_at_9 α).symm
  have h_lhs : delta (cupAW 5 3 1 α β) i
             = delta (cupAW 5 3 1 (decomp_5_3 α) β) i := by
    apply delta_pointwise_eq; intro j
    exact cupAW_pointwise_eq α (decomp_5_3 α) β β h_α_pw (fun _ => rfl) j
  have h_rhs1 : cupAW 5 4 1 (delta α) β i
              = cupAW 5 4 1 (delta (decomp_5_3 α)) β i := by
    have h_delta_α_pw : ∀ j, delta α j = delta (decomp_5_3 α) j :=
      fun j => delta_pointwise_eq α (decomp_5_3 α) h_α_pw j
    exact cupAW_pointwise_eq (delta α) (delta (decomp_5_3 α)) β β
            h_delta_α_pw (fun _ => rfl) i
  have h_rhs2 : cupAW 5 3 2 α (delta β) i
              = cupAW 5 3 2 (decomp_5_3 α) (delta β) i :=
    cupAW_pointwise_eq α (decomp_5_3 α) (delta β) (delta β)
      h_α_pw (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  unfold decomp_5_3
  rw [delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      h_components ⟨0, by decide⟩, h_components ⟨1, by decide⟩,
      h_components ⟨2, by decide⟩, h_components ⟨3, by decide⟩,
      h_components ⟨4, by decide⟩, h_components ⟨5, by decide⟩,
      h_components ⟨6, by decide⟩, h_components ⟨7, by decide⟩,
      h_components ⟨8, by decide⟩, h_components ⟨9, by decide⟩]
  exact combine_10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- ★★★★★★ **Universal Cup-AW Leibniz at (5, 3, 1)** — STRICT
    ∅-AXIOM.  Sister of (5, 2, 1) at the codim-3 α stratum;
    closes the codim-3 stratum's leftmost β-degree of the
    (5, 3, b) family.  α-side decomposition: 10 basis
    components (V5_3Decomp + combine_10), β-side pattern:
    5 Bool components (Prop51). -/
theorem leibniz_universal_5_3_1
    (α : Cochain 5 3) (β : Cochain 5 1) (i : Fin (binom 5 4)) :
    delta (cupAW 5 3 1 α β) i
      = xor (cupAW 5 4 1 (delta α) β i)
            (cupAW 5 3 2 α (delta β) i) :=
  leibniz_via_α_decomp α β i (h_components_α α β i)

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1
