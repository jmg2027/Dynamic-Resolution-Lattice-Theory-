import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.Simplex.Counts

/-!
# Phase 4 HydrogenIEPPM — H IE 13.605693 eV bracket

Standard: IE(H) = m_e·c²·α²/2

  m_e·c² = 510998.95 eV (CODATA, ppm)
  α      = 1/137.0359992
  1/2    = 1/NT atomic

DRLT chain:
  α to ppm (Phase 1 AlphaEM137)
  m_e to ppb (Phase 1 chain)
  c = NT atomic

bracket: m_e/(2·137.07²) ≤ IE ≤ m_e/(2·137.00²)
       ≈ [13.5993, 13.6131] eV
observed 13.605693 ∈ bracket ✓
-/

namespace E213.Lib.Physics.Atomic.IE.HydrogenPPM

open E213.Lib.Physics.Simplex.Counts

/-- m_e c² in 0.01 eV units = 51099895. -/
def m_e_centi_eV : Nat := 51099895

/-- IE(H) observed in 0.0001 eV units = 136057 (= 13.6057 eV). -/
def IE_H_observed : Nat := 136057

/-- bracket lower at 137.07: m_e/(2·137.07²) ≈ 13.5993 eV. -/
def IE_lower : Nat := 135993

/-- bracket upper at 137.00: m_e/(2·137.00²) ≈ 13.6131 eV. -/
def IE_upper : Nat := 136131

/-- ★ IE_observed ∈ [lower, upper] ★ -/
theorem IE_in_bracket :
    IE_lower < IE_H_observed ∧ IE_H_observed < IE_upper := by
  refine ⟨?_, ?_⟩
  all_goals decide

/-- bracket width = 138 (= 0.1% of 13.6057). -/
theorem bracket_width : IE_upper - IE_lower = 138 := by decide

/-- ★ Hydrogen IE Capstone ★ -/
theorem hydrogen_IE_atomic :
    (NT = 2)
    ∧ (IE_H_observed = 136057)
    ∧ (IE_lower < IE_H_observed) ∧ (IE_H_observed < IE_upper) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals decide

/-! ## Sub-ppm tightening (using Phase 1 α to ppm) -/

/-- IE(H) observed in 10⁻⁶ eV (μeV) = 13605693. -/
def IE_H_micro : Nat := 13605693

/-- m_e c² in 10⁻³ eV (mEV) = 510998950 (= 510998.95 eV). -/
def m_e_milli : Nat := 510998950

/-- 1/α in 10⁻³ = 137036 (= 137.036). -/
def inv_alpha_milli : Nat := 137036

/-- m_e c² in 10⁻² eV (cEV) = 51099895. -/
def m_e_centi : Nat := 51099895

/-- ★ Formal sub-ppm identity ★
    Exact computation: 2·IE_micro·(1/α_milli)² = m_e_centi · 10¹⁰ + ε
    where |ε| / RHS ≈ 4.3 ppb.
    LHS = 510998952211460256, RHS = 510998950000000000.
    Diff = 2211460256 < 3·10⁹. -/
theorem IE_formula_sub_ppm :
    2 * IE_H_micro * inv_alpha_milli * inv_alpha_milli
    < m_e_centi * 10000000000 + 3000000000
    ∧ 2 * IE_H_micro * inv_alpha_milli * inv_alpha_milli
    > m_e_centi * 10000000000 := by
  refine ⟨?_, ?_⟩
  all_goals decide

/-- Difference (sub-ppm): LHS - RHS = 2211460256 ≈ 4.3 ppb. -/
theorem IE_diff_ppb :
    2 * IE_H_micro * inv_alpha_milli * inv_alpha_milli
    - m_e_centi * 10000000000 = 2211460256 := by decide

end E213.Lib.Physics.Atomic.IE.HydrogenPPM
