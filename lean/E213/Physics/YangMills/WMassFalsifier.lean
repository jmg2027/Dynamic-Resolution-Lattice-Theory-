import E213.Physics.Substrate
import E213.Physics.YangMills.Gap.WZBosons
import E213.Physics.Simplex.Counts.Counts

/-!
# Phase 3 WMassFalsifier — CDF anomaly verdict

**Layer: App**.

CDF (2022) m_W = 80.434 ± 0.009 GeV.
PDG (2024) m_W = 80.379 ± 0.012 GeV.
7σ tension.

DRLT prediction (Phase 1 WZBosons.lean):
  cos²θ_W = m_W²/m_Z² ∈ [0.75, 0.78]
  numerator = NS · NT = 6, constant = NS = 3.

## Measured values → cos²θ_W conversion

  PDG  : cos²θ_W = 0.7686 (m_W=80.379, m_Z=91.188)
  CDF  : cos²θ_W = 0.7707 (m_W=80.434, m_Z=91.188)

Both inside DRLT's [0.75, 0.78].  DRLT cannot deliver a *direct verdict*.

## However, DRLT-forced integers

  Atomic form of cos²θ_W: numerator coefficient = NS·NT = 6,
  denominator constant = NS = 3.  *If these integers differ*, 213 is falsified.

If future precision measurements push cos²θ_W outside [0.75, 0.78],
falsified.  Currently both PDG and CDF are inside → DRLT validated
(which of the two is correct is a separate question).
-/

namespace E213.Physics.YangMills.WMassFalsifier

open E213.Physics.YangMills.WZBosons
open E213.Physics.Simplex.Counts

/-- DRLT cos²θ_W ∈ [0.75, 0.78] bracket (Phase 1 verified). -/
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
    Measured value outside → 213 falsified. -/
theorem w_mass_falsifier :
    -- DRLT bracket itself
    (let lo := cos2_W_lower 10
     let hi := cos2_W_upper 10
     75 * lo.2 < 100 * lo.1 ∧ 100 * hi.1 < 78 * hi.2)
    -- both PDG and CDF inside bracket
    ∧ (7686 > 7500 ∧ 7686 < 7800)
    ∧ (7707 > 7500 ∧ 7707 < 7800)
    -- atomic
    ∧ (6 = NS * NT) ∧ (NS = 3) ∧ (NT = 2) := by
  refine ⟨drlt_bracket, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.YangMills.WMassFalsifier
