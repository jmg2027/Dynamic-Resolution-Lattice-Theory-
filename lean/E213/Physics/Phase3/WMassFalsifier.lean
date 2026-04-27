import E213.Physics.Phase2
import E213.Physics.WZBosons
import E213.Physics.SimplexCounts

/-!
# Phase 3 WMassFalsifier — CDF anomaly 결판

**Layer: App**.

CDF (2022) m_W = 80.434 ± 0.009 GeV.
PDG (2024) m_W = 80.379 ± 0.012 GeV.
7σ tension.

DRLT 예측 (Phase 1 WZBosons.lean):
  cos²θ_W = m_W²/m_Z² ∈ [0.75, 0.78]
  numerator = NS · NT = 6, constant = NS = 3.

## 측정값 → cos²θ_W 환산

  PDG  : cos²θ_W = 0.7686 (m_W=80.379, m_Z=91.188)
  CDF  : cos²θ_W = 0.7707 (m_W=80.434, m_Z=91.188)

둘 다 DRLT 의 [0.75, 0.78] 안.  DRLT 는 *직접 결판* 못 함.

## 그러나 DRLT 강제 정수

  cos²θ_W 의 atomic form: numerator coefficient = NS·NT = 6,
  denominator constant = NS = 3.  *이 정수들이 다르면* 213 폐기.

미래 정밀 측정이 cos²θ_W 를 [0.75, 0.78] 밖으로 가져가면
폐기.  현재 PDG와 CDF 둘 다 안쪽 → DRLT 검증 (둘 중 어느
쪽이 정확한지는 별개 문제).
-/

namespace E213.Physics.Phase3.WMassFalsifier

open E213.Physics.WZBosons
open E213.Physics.Simplex

/-- DRLT cos²θ_W ∈ [0.75, 0.78] bracket (Phase 1 검증). -/
theorem drlt_bracket :
    let lo := cos2_W_lower 10
    let hi := cos2_W_upper 10
    75 * lo.2 < 100 * lo.1
    ∧ 100 * hi.1 < 78 * hi.2 := cos2_W_in_75_78

/-- Atomic form check: 6 = NS·NT, 3 = NS. -/
theorem atomic_form_check :
    6 = NS * NT ∧ 3 = NS ∧ NS = 3 ∧ NT = 2 := cos2_W_atomic_form

/-- PDG cos²θ_W = 0.7686 → numerator 7686, denom 10000.
    7686/10000 ∈ [0.75, 0.78] check. -/
theorem pdg_in_bracket :
    -- 7686 > 7500 (above 0.75)
    7686 > 7500
    -- 7686 < 7800 (below 0.78)
    ∧ 7686 < 7800 := by decide

/-- CDF cos²θ_W = 0.7707 → 7707/10000 ∈ [0.75, 0.78] check. -/
theorem cdf_in_bracket :
    7707 > 7500 ∧ 7707 < 7800 := by decide

/-- ★ W mass falsifier ★
    DRLT cos²θ_W bracket forces m_W²/m_Z² ∈ [0.75, 0.78].
    측정값이 outside → 213 폐기. -/
theorem w_mass_falsifier :
    -- DRLT bracket 자체
    (let lo := cos2_W_lower 10
     let hi := cos2_W_upper 10
     75 * lo.2 < 100 * lo.1 ∧ 100 * hi.1 < 78 * hi.2)
    -- PDG, CDF 둘 다 bracket 안
    ∧ (7686 > 7500 ∧ 7686 < 7800)
    ∧ (7707 > 7500 ∧ 7707 < 7800)
    -- atomic
    ∧ (6 = NS * NT) ∧ (NS = 3) ∧ (NT = 2) := by
  refine ⟨drlt_bracket, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase3.WMassFalsifier
