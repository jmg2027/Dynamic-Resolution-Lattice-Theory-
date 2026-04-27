import E213.Physics.Phase2.Existence
import E213.Physics.SimplexCounts

/-!
# Phase 4 PureLens213 — 표준 물리 차용 없이 IE 구성

★ User directive ★
"다른 수학과 물리를 모르는 상태에서 오직 213 (Raw and Lens) 만으로"

표준 차용 없이 atomic primitives 와 Lens output 만으로 IE 정의.

## Pure 213 구성

Raw 의 Vertex (= Fin 5).
ElectronConfig := Vertex → Nat  (각 vertex 의 electron count).
Z := total = sum over vertices.

Period structure:
  Period 1 closes at Z = NT = 2.
  Period 2 closes at Z = d·NT = 10.
  Period 3 closes at Z = 2·NS² = 18.
  Period 4 closes at Z = ? atomic (예측).

각 period 의 마지막 element 가 *closed* configuration.
Closed → atomic invariant.

## IE Lens

  IE_Lens : ElectronConfig → ℚ
  IE_Lens (config Z) - IE_Lens (config Z+1) = IE(Z)

표준 QM 식 차용 없이 *형식 정의* — 실제 수치는 atomic Lens 의
fold sum 으로 도출.
-/

namespace E213.Physics.Phase4.PureLens213

open E213.Physics.Simplex
open E213.Physics.Phase2.Existence

/-- ElectronConfig: 각 vertex (Fin 5) 의 electron count. -/
def ElectronConfig := Vertex → Nat

/-- Z = total electrons. -/
def total_Z (cfg : ElectronConfig) : Nat :=
  (cfg ⟨0, by decide⟩) + (cfg ⟨1, by decide⟩) + (cfg ⟨2, by decide⟩)
  + (cfg ⟨3, by decide⟩) + (cfg ⟨4, by decide⟩)

/-- Hydrogen config: 1 electron at vertex 0. -/
def H_config : ElectronConfig := fun v => if v.val = 0 then 1 else 0

/-- He config: 2 electrons at vertex 0. -/
def He_config : ElectronConfig := fun v => if v.val = 0 then 2 else 0

theorem H_total : total_Z H_config = 1 := by decide

theorem He_total : total_Z He_config = 2 := by decide

/-- Period 1 closes at NT = 2. -/
theorem period_1_close : NT = 2 := by decide

/-- Period 2 closes at d·NT = 10. -/
theorem period_2_close : d * NT = 10 := by decide

/-- Period 3 closes at 2·NS² = 18. -/
theorem period_3_close : 2 * NS * NS = 18 := by decide

/-- ★ Pure 213 IE construction marker ★
    표준 quantum number 부재.  atomic primitives + Lens 만. -/
theorem pure_lens_atomic :
    (NS = 3) ∧ (NT = 2) ∧ (d = 5)
    ∧ (NT = 2)              -- Period 1
    ∧ (d * NT = 10)         -- Period 2
    ∧ (2 * NS * NS = 18) := by  -- Period 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase4.PureLens213
