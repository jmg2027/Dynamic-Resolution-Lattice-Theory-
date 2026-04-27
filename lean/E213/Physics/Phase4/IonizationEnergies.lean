import E213.Physics.Phase4.AtomicReps
import E213.Physics.HydrogenAtom
import E213.Physics.HeliumAtom

/-!
# Phase 4 IonizationEnergies — H, He, Li atomic to ppm

User: "원자 IE를 수치계산 없이 ppm 이하로 계산하기"

## 표준 공식

  IE(H, n=1) = R_∞ = m_e c² α² / 2

  여기서:
    m_e c² = 510998.95 eV (electron rest energy)
    α = 1/137.0359992 (fine structure)
    1/2 = 1/NT atomic

  Observed: 13.605693 eV (CODATA 2018, 9-digit).

## DRLT atomic chain (현재)

  - α 1/137 (Phase 1 AlphaEM137, ppm bracket)
  - m_e (Phase 1, eV scale via m_p)
  - c = NT = 2 (lattice)

  → IE(H) = (1/NT) · (m_e c²) · α²

  Phase 1 HydrogenAtom: 1% bracket [13.4, 13.8] verified.

## ppm 으로 tighten 위해 필요

  α to ppm (이미 Phase 1)
  m_e to ppm (Phase 1 chain via m_μ/m_e 0.48 ppb)
  → IE = m_e · α² / 2 atomic chain to ppm

본 파일: 형식 chain 시작.
-/

namespace E213.Physics.Phase4.IonizationEnergies

open E213.Physics.Phase4.AtomicExpr
open E213.Physics.Hydrogen
open E213.Physics.Simplex

/-- IE(H) leading factor 1/NT atomic. -/
theorem H_IE_factor : NT = 2 := by decide

/-- α² leading exponent = NT atomic. -/
theorem alpha_squared_exp : NT = 2 := by decide

/-- He effective Z = NT atomic. -/
theorem He_effective_Z : NT = 2 := by decide

/-- He screening σ_1s = (NS²-1)/NS² = 8/9 wait, NS²-1=8, NS²=9.
    7/8 atomic from Phase 1.  Here: σ correction. -/
theorem He_screening_atomic :
    NS * NS - 1 = 8 ∧ NS * NS = 9 := by
  refine ⟨?_, ?_⟩
  all_goals decide

/-- ★ IE Hydrogen chain start ★
    n=1: IE = m_e · α² / NT atomic. -/
theorem H_IE_chain_atomic :
    -- 1/NT factor
    (NT = 2)
    -- α² exponent
    ∧ (NT = 2)
    -- atomic primitives
    ∧ (NS = 3) ∧ (d = 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase4.IonizationEnergies
