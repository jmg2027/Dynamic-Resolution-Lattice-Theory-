/-
  YangMills/DeficitAngle.lean

  The deficit angle delta_AAA = Real.pi, DERIVED from Fubini-Study geometry.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import YangMills.Basic

set_option autoImplicit false

open Real

namespace DRLT.YangMills

/-! ## 1. Fubini-Study Dihedral Angles (defined via arccos) -/

/-- Dihedral angle 1: arccos|<T1|T2>| = arccos 0 (orthonormal) -/
noncomputable def fsTheta1 : Real := arccos 0

/-- Dihedral angle 2: arccos|<T1|T3>| = arccos(cos gamma) -/
noncomputable def fsTheta2 (gamma : Real) : Real := arccos (cos gamma)

/-- Dihedral angle 3: arccos|<T2|T3>| = arccos(sin gamma) -/
noncomputable def fsTheta3 (gamma : Real) : Real := arccos (sin gamma)

/-! ## 2. Computing Each Angle (via Mathlib) -/

/-- theta1 = pi/2 -/
theorem fsTheta1_eq : fsTheta1 = Real.pi / 2 := Real.arccos_zero

/-- theta2 = gamma for gamma in [0, pi/2] -/
theorem fsTheta2_eq (gamma : Real) (h0 : 0 ≤ gamma) (hpi : gamma ≤ Real.pi / 2) :
    fsTheta2 gamma = gamma := by
  unfold fsTheta2
  exact arccos_cos h0 (by linarith [Real.pi_pos])

/-- sin x = cos(pi/2 - x) -/
theorem sin_eq_cos_compl (gamma : Real) :
    sin gamma = cos (Real.pi / 2 - gamma) :=
  (cos_pi_div_two_sub gamma).symm

/-- theta3 = pi/2 - gamma for gamma in [0, pi/2] -/
theorem fsTheta3_eq (gamma : Real) (h0 : 0 ≤ gamma) (hpi : gamma ≤ Real.pi / 2) :
    fsTheta3 gamma = Real.pi / 2 - gamma := by
  unfold fsTheta3
  rw [sin_eq_cos_compl]
  exact arccos_cos (by linarith) (by linarith [Real.pi_pos])

/-! ## 3. The Deficit Angle = pi (MAIN THEOREM) -/

/-- THE DIHEDRAL SUM: theta1 + theta2 + theta3 = pi.
    Each angle is DERIVED from arccos, not assumed. -/
theorem fubini_dihedral_sum (gamma : Real) (h0 : 0 ≤ gamma)
    (hpi : gamma ≤ Real.pi / 2) :
    fsTheta1 + fsTheta2 gamma + fsTheta3 gamma = Real.pi := by
  rw [fsTheta1_eq, fsTheta2_eq gamma h0 hpi, fsTheta3_eq gamma h0 hpi]
  ring

/-- THE DEFICIT ANGLE: delta = 2pi - pi = pi -/
theorem deficit_angle_eq_pi (gamma : Real) (h0 : 0 ≤ gamma)
    (hpi : gamma ≤ Real.pi / 2) :
    2 * Real.pi - (fsTheta1 + fsTheta2 gamma + fsTheta3 gamma) = Real.pi := by
  rw [fubini_dihedral_sum gamma h0 hpi]; ring

/-- The deficit angle is strictly positive -/
theorem deficit_angle_pos (gamma : Real) (h0 : 0 ≤ gamma)
    (hpi : gamma ≤ Real.pi / 2) :
    fsTheta1 + fsTheta2 gamma + fsTheta3 gamma < 2 * Real.pi := by
  rw [fubini_dihedral_sum gamma h0 hpi]; linarith [Real.pi_pos]

/-! ## 4. Universality -/

/-- delta is independent of gamma -/
theorem deficit_angle_universal (g1 g2 : Real)
    (h01 : 0 ≤ g1) (hp1 : g1 ≤ Real.pi / 2)
    (h02 : 0 ≤ g2) (hp2 : g2 ≤ Real.pi / 2) :
    2 * Real.pi - (fsTheta1 + fsTheta2 g1 + fsTheta3 g1) =
    2 * Real.pi - (fsTheta1 + fsTheta2 g2 + fsTheta3 g2) := by
  rw [fubini_dihedral_sum g1 h01 hp1, fubini_dihedral_sum g2 h02 hp2]

/-! ## 5. All Dihedral Angles Are in [0, pi] -/

theorem theta1_range : 0 ≤ fsTheta1 ∧ fsTheta1 ≤ Real.pi := by
  rw [fsTheta1_eq]; constructor <;> linarith [Real.pi_pos]

theorem theta2_range (gamma : Real) (h0 : 0 ≤ gamma) (hpi : gamma ≤ Real.pi / 2) :
    0 ≤ fsTheta2 gamma ∧ fsTheta2 gamma ≤ Real.pi := by
  rw [fsTheta2_eq gamma h0 hpi]; exact ⟨h0, by linarith [Real.pi_pos]⟩

theorem theta3_range (gamma : Real) (h0 : 0 ≤ gamma) (hpi : gamma ≤ Real.pi / 2) :
    0 ≤ fsTheta3 gamma ∧ fsTheta3 gamma ≤ Real.pi := by
  rw [fsTheta3_eq gamma h0 hpi]; constructor <;> linarith [Real.pi_pos]

/-! ## 6. Dimensional Dependence -/

theorem temporal_basis_size : nT = 2 := rfl

theorem three_simplices_from_nT :
    Nat.choose (nT + 1) 2 = 3 := by native_decide

end DRLT.YangMills
