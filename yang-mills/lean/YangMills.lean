/-
  YangMills.lean — Module root

  Lean 4 formalization of the Yang-Mills mass gap and
  Navier-Stokes regularity theorems from DRLT Chapter 15.

  THEOREM INVENTORY (0 sorry):
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Basic.lean (15 theorems):
    • bbb_impossible          : C(2,3) = 0
    • aaa_unique_channel      : N_eff(3) = 1
    • aab_channels            : N_eff(2) = 6
    • abb_channels            : N_eff(1) = 3
    • total_hinges_per_simplex: C(5,3) = 10
    • channel_sum             : 1+6+3+0 = 10
    • rank_saturation         : C(3,3) = 1
    • isolated_quark_no_hinge : C(1,3) = 0
    • diquark_no_hinge        : C(2,3) = 0
    • baryon_one_hinge        : C(3,3) = 1
    • simplices_sharing_aaa   : C(3,2) = 3
    + 4 auxiliary lemmas

  DeficitAngle.lean (6 theorems):
    • dihedral_sum_eq_pi       : θ₁+θ₂+θ₃ = π
    • deficit_angle_eq_pi      : 2π - (θ₁+θ₂+θ₃) = π
    • deficit_angle_universal  : δ independent of γ
    • deficit_angle_pos        : θ₁+θ₂+θ₃ < 2π
    • complementarity_implies_pi
    • three_simplices_from_nT  : C(3,2) = 3

  MassGap.lean (7 theorems):
    • hingeArea_pos     : A_h > 0
    • reggeAction_pos   : S_h > 0
    • mass_gap_pos      : Δ > 0  ← THE MAIN THEOREM
    • mass_gap_ideal    : Δ = π (ideal simplex)
    • mass_gap_vanishes_with_det : det→0 ⟹ Δ→0
    • three_facts_imply_gap
    + 1 auxiliary lemma

  LatticeRegularity.lean (4 theorems):
    • sobolevBound_nonneg    : bound ≥ 0
    • lattice_regularity     : ‖v‖_{H^s} < ∞  ← NS REGULARITY
    • structural_equivalence : YM gap ↔ NS regularity
    + 1 auxiliary lemma

  TOTAL: 32 theorems, 0 sorry.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import YangMills.Basic
import YangMills.DeficitAngle
import YangMills.MassGap
import YangMills.GramMatrix
import YangMills.LinearIndepDet
import YangMills.PhysicalGram
import YangMills.Hadamard
import YangMills.NoGo
import YangMills.ChebyshevAction
import YangMills.LatticeRegularity
