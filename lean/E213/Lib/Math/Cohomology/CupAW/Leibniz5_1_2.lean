import E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2_BasisDecomp
import E213.Lib.Math.Cohomology.CupAW.LeibnizDecomp
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21
import E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift
import E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
import E213.Lib.Math.Cohomology.Universal.Prop52
import E213.Lib.Math.Cohomology.Bridge.XorPairCombine
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW Leibniz at (5, 1, 2) — universal lift via bilinearity

Closes the universal (5, 1, 2) Cup-AW Leibniz identity that
the full ∀-pattern decide could not handle (Phase 10 OOM
analysis).  The closure proceeds in three steps:

  1. Per-basis facts (from `Leibniz5_1_2_BasisDecomp`): five
     decided Leibniz identities at `α = basis 5 1 ⟨k⟩` for
     `k ∈ {0..4}`.
  2. Per-component handling: for each `k`, the bz5_1 component
     `bz5_1 α k` is either zero (when `α k = false`, collapse
     via `cupAW_zero_left`) or `basis 5 1 k` (when `α k = true`,
     use per-basis fact + pointwise transport).
  3. α-decomp lens: combine the 5 per-component facts via the
     bilinearity chain (`cupAW_add_left` + `delta_cupAW_add_left`
     + `cupAW_delta_add_left`) and `combine_5`.

Mirrors `Leibniz21Final` (which closes (5, 2, 1) via β-decomp);
adapted for the α-side at degree 1.  Strict ∅-axiom.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.V5_1DecompR (decomp_5_1 bz5_1)
open E213.Lib.Math.Cohomology.Bridge.XorPairCombine (combine_5)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.CupAW.Zero
  (cupAW_zero_left cupAW_zero_right delta_zero)
open E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
  (decomp_step_at_0 decomp_step_at_1 decomp_step_at_2
   decomp_step_at_3 decomp_step_at_4)
open E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
  (delta_cupAW_add_left cupAW_delta_add_left)
open E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
  (bz5_1_false_at bz5_1_true_at)
open E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2_BasisDecomp
  (leibniz_basis_5_1_2_at_0 leibniz_basis_5_1_2_at_1
   leibniz_basis_5_1_2_at_2 leibniz_basis_5_1_2_at_3
   leibniz_basis_5_1_2_at_4)
open E213.Lib.Math.Cohomology.Universal.Prop52 renaming pattern → patternE
open E213.Tactic.NatHelper (cases_lt_five)

/-! ## §1 — Left-factor decomp helpers at (5, 1, 2) -/

/-- Zero-collapse on the LEFT factor at (5, 1, 2).  If
    `γ : Cochain 5 1` is pointwise zero, the Leibniz identity
    collapses to `false = xor false false`. -/
private theorem leibniz_zero_collapse_left
    (γ : Cochain 5 1) (β : Cochain 5 2)
    (i : Fin (binom 5 3))
    (h : ∀ j, γ j = Cochain.zero 5 1 j) :
    delta (cupAW 5 1 2 γ β) i
      = xor (cupAW 5 2 2 (delta γ) β i)
            (cupAW 5 1 3 γ (delta β) i) := by
  have h_delta_γ : ∀ j, delta γ j = Cochain.zero 5 2 j :=
    fun j => (delta_pointwise_eq _ _ h j).trans (delta_zero 5 1 j)
  have h_lhs : delta (cupAW 5 1 2 γ β) i = false := by
    have h_cup_pw : ∀ j, cupAW 5 1 2 γ β j = Cochain.zero 5 2 j := fun j => by
      have step :=
        cupAW_pointwise_eq γ (Cochain.zero 5 1) β β h (fun _ => rfl) j
      exact step.trans (cupAW_zero_left 5 1 2 β j)
    exact (delta_pointwise_eq _ _ h_cup_pw i).trans (delta_zero 5 2 i)
  have h_rhs1 : cupAW 5 2 2 (delta γ) β i = false := by
    have step :=
      cupAW_pointwise_eq (delta γ) (Cochain.zero 5 2) β β
        h_delta_γ (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 2 2 β i)
  have h_rhs2 : cupAW 5 1 3 γ (delta β) i = false := by
    have step :=
      cupAW_pointwise_eq γ (Cochain.zero 5 1) (delta β) (delta β)
        h (fun _ => rfl) i
    exact step.trans (cupAW_zero_left 5 1 3 (delta β) i)
  rw [h_lhs, h_rhs1, h_rhs2]; rfl

/-- Pointwise transport on the LEFT factor at (5, 1, 2). -/
private theorem leibniz_pointwise_transport_left
    (γ γ' : Cochain 5 1) (β : Cochain 5 2)
    (i : Fin (binom 5 3))
    (h : ∀ j, γ j = γ' j)
    (basis_leib : delta (cupAW 5 1 2 γ' β) i
                = xor (cupAW 5 2 2 (delta γ') β i)
                      (cupAW 5 1 3 γ' (delta β) i)) :
    delta (cupAW 5 1 2 γ β) i
      = xor (cupAW 5 2 2 (delta γ) β i)
            (cupAW 5 1 3 γ (delta β) i) := by
  have h_delta : ∀ j, delta γ j = delta γ' j :=
    fun j => delta_pointwise_eq _ _ h j
  have h_lhs : delta (cupAW 5 1 2 γ β) i = delta (cupAW 5 1 2 γ' β) i := by
    apply delta_pointwise_eq
    intro j
    exact cupAW_pointwise_eq γ γ' β β h (fun _ => rfl) j
  have h_rhs1 : cupAW 5 2 2 (delta γ) β i = cupAW 5 2 2 (delta γ') β i :=
    cupAW_pointwise_eq (delta γ) (delta γ') β β h_delta (fun _ => rfl) i
  have h_rhs2 : cupAW 5 1 3 γ (delta β) i = cupAW 5 1 3 γ' (delta β) i :=
    cupAW_pointwise_eq γ γ' (delta β) (delta β) h (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  exact basis_leib

/-! ## §2 — Per-basis universal-β lift

The per-basis facts `leibniz_basis_5_1_2_at_k` are quantified
over the β-pattern (10 Bool variables).  Lift to arbitrary
`β : Cochain 5 2` via `Prop52.pattern_eq_at` +
`leibniz_pointwise_lift`. -/

/-- Per-basis Leibniz at α = basis 5 1 ⟨k⟩, lifted to arbitrary β.
    PURE corollary of the basis decide + `leibniz_pointwise_lift`. -/
private theorem leibniz_basis_universal (k : Fin 5)
    (β : Cochain 5 2) (i : Fin (binom 5 3)) :
    delta (cupAW 5 1 2 (basis 5 1 k) β) i
      = xor (cupAW 5 2 2 (delta (basis 5 1 k)) β i)
            (cupAW 5 1 3 (basis 5 1 k) (delta β) i) := by
  let pβ := patternE (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                     (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                     (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
                     (β ⟨6, by decide⟩) (β ⟨7, by decide⟩)
                     (β ⟨8, by decide⟩) (β ⟨9, by decide⟩)
  rcases k with ⟨n, hn⟩
  rcases (cases_lt_five hn) with rfl | rfl | rfl | rfl | rfl
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 1 2 (basis 5 1 ⟨0, by decide⟩) β
      (basis 5 1 ⟨0, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop52.pattern_eq_at β)
      (leibniz_basis_5_1_2_at_0
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
        (β ⟨6, by decide⟩) (β ⟨7, by decide⟩) (β ⟨8, by decide⟩)
        (β ⟨9, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 1 2 (basis 5 1 ⟨1, by decide⟩) β
      (basis 5 1 ⟨1, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop52.pattern_eq_at β)
      (leibniz_basis_5_1_2_at_1
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
        (β ⟨6, by decide⟩) (β ⟨7, by decide⟩) (β ⟨8, by decide⟩)
        (β ⟨9, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 1 2 (basis 5 1 ⟨2, by decide⟩) β
      (basis 5 1 ⟨2, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop52.pattern_eq_at β)
      (leibniz_basis_5_1_2_at_2
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
        (β ⟨6, by decide⟩) (β ⟨7, by decide⟩) (β ⟨8, by decide⟩)
        (β ⟨9, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 1 2 (basis 5 1 ⟨3, by decide⟩) β
      (basis 5 1 ⟨3, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop52.pattern_eq_at β)
      (leibniz_basis_5_1_2_at_3
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
        (β ⟨6, by decide⟩) (β ⟨7, by decide⟩) (β ⟨8, by decide⟩)
        (β ⟨9, by decide⟩) i)
  · exact E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift.leibniz_pointwise_lift
      5 1 2 (basis 5 1 ⟨4, by decide⟩) β
      (basis 5 1 ⟨4, by decide⟩) pβ i i i
      (fun _ => rfl)
      (E213.Lib.Math.Cohomology.Universal.Prop52.pattern_eq_at β)
      (leibniz_basis_5_1_2_at_4
        (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
        (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
        (β ⟨6, by decide⟩) (β ⟨7, by decide⟩) (β ⟨8, by decide⟩)
        (β ⟨9, by decide⟩) i)

/-! ## §3 — Per-bz5_1-component Leibniz via case-split -/

/-- Per-α-component Leibniz at `α = bz5_1 α' k`.  Case-split on
    `α' k`: false → zero-collapse; true → pointwise transport
    to per-basis fact. -/
private theorem h_components_α (α : Cochain 5 1) (β : Cochain 5 2)
    (i : Fin (binom 5 3)) (k : Fin 5) :
    delta (cupAW 5 1 2 (bz5_1 α k) β) i
      = xor (cupAW 5 2 2 (delta (bz5_1 α k)) β i)
            (cupAW 5 1 3 (bz5_1 α k) (delta β) i) := by
  cases hα : α k
  · exact leibniz_zero_collapse_left
      (bz5_1 α k) β i (bz5_1_false_at α k hα)
  · exact leibniz_pointwise_transport_left
      (bz5_1 α k) (basis 5 1 k) β i (bz5_1_true_at α k hα)
      (leibniz_basis_universal k β i)

/-! ## §4 — α-decomp lens at (5, 1, 2) and universal theorem -/

/-- ★ **α-decomp lens at (5, 1, 2)**.  Given Leibniz on each
    `bz5_1 α k` component, conclude on the full `α`.  Sister to
    `LeibnizAlgLift21.leibniz_via_β_decomp_21` — same structural
    pattern, applied to the α-side at degree 1. -/
private theorem leibniz_via_α_decomp
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3))
    (h_components : ∀ k : Fin 5,
      delta (cupAW 5 1 2 (bz5_1 α k) β) i
        = xor (cupAW 5 2 2 (delta (bz5_1 α k)) β i)
              (cupAW 5 1 3 (bz5_1 α k) (delta β) i)) :
    delta (cupAW 5 1 2 α β) i
      = xor (cupAW 5 2 2 (delta α) β i)
            (cupAW 5 1 3 α (delta β) i) := by
  have h_α_pw : ∀ j, α j = decomp_5_1 α j := by
    intro j; rcases j with ⟨n, hn⟩
    rcases (cases_lt_five hn) with rfl | rfl | rfl | rfl | rfl
    · exact (decomp_step_at_0 α).symm
    · exact (decomp_step_at_1 α).symm
    · exact (decomp_step_at_2 α).symm
    · exact (decomp_step_at_3 α).symm
    · exact (decomp_step_at_4 α).symm
  have h_lhs : delta (cupAW 5 1 2 α β) i
             = delta (cupAW 5 1 2 (decomp_5_1 α) β) i := by
    apply delta_pointwise_eq; intro j
    exact cupAW_pointwise_eq α (decomp_5_1 α) β β h_α_pw (fun _ => rfl) j
  have h_rhs1 : cupAW 5 2 2 (delta α) β i
              = cupAW 5 2 2 (delta (decomp_5_1 α)) β i := by
    have h_delta_α_pw : ∀ j, delta α j = delta (decomp_5_1 α) j :=
      fun j => delta_pointwise_eq α (decomp_5_1 α) h_α_pw j
    exact cupAW_pointwise_eq (delta α) (delta (decomp_5_1 α)) β β
            h_delta_α_pw (fun _ => rfl) i
  have h_rhs2 : cupAW 5 1 3 α (delta β) i
              = cupAW 5 1 3 (decomp_5_1 α) (delta β) i :=
    cupAW_pointwise_eq α (decomp_5_1 α) (delta β) (delta β)
      h_α_pw (fun _ => rfl) i
  rw [h_lhs, h_rhs1, h_rhs2]
  unfold decomp_5_1
  rw [delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left,
      h_components ⟨0, by decide⟩, h_components ⟨1, by decide⟩,
      h_components ⟨2, by decide⟩, h_components ⟨3, by decide⟩,
      h_components ⟨4, by decide⟩]
  exact combine_5 _ _ _ _ _ _ _ _ _ _

/-- ★★★★★★ **Universal Cup-AW Leibniz at (5, 1, 2)** — STRICT
    ∅-AXIOM.  Closes the bidegree that defeated four full-pattern
    decide strategies via the per-basis breakthrough + bilinearity
    chain.

    Sister to `Leibniz21Final.leibniz_universal_5_2_1` (β-decomp
    at (5, 2, 1)) — same algebraic structure on the α-side at
    α-degree 1. -/
theorem leibniz_universal_5_1_2
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3)) :
    delta (cupAW 5 1 2 α β) i
      = xor (cupAW 5 2 2 (delta α) β i)
            (cupAW 5 1 3 α (delta β) i) :=
  leibniz_via_α_decomp α β i (h_components_α α β i)

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2
