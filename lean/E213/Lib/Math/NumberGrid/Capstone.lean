import E213.Lib.Math.NumberGrid.FSMGradeTaxonomy
import E213.Lib.Math.NumberGrid.HorizontalAxis
import E213.Lib.Math.NumberGrid.TwoDimGrid

/-!
# G41 Capstone — 2D Number-System Grid (∅-axiom)

5 cluster witnesses + total bundle.

Mingu's insight: number systems form a **2D grid**, not a linear
chain.  Vertical axis = CD tower level; horizontal axis = FSM
recognizability grade.  Both read out at index 25 (bare arithmetic
values) on d=5 Lens application.
-/

namespace E213.Lib.Math.NumberGrid.Capstone

open E213.Lib.Math.NumberGrid.FSMGradeTaxonomy
  (fsmGradeStates grade_0_states grade_1_states grade_25_states
   grade_26_excess grade_succ_ratio)
open E213.Lib.Math.NumberGrid.HorizontalAxis
  (NumberType gradeToType grade0_natural grade1_integer
   grade5_rational grade20_algebraic grade25_substrate)
open E213.Lib.Math.NumberGrid.TwoDimGrid
  (gridSize grid_size_eq_625 cell_naturals cell_integers
   cell_complex_rational cell_high_grade index_25_readings)
open E213.Lib.Math.SignedCut.CD.CDTowerLevel (levelDim)

/-- ★ **FSM grade taxonomy witness** — 0/1/25 grades. -/
theorem fsm_grades_witness :
    fsmGradeStates 0 = 1
    ∧ fsmGradeStates 1 = 5
    ∧ fsmGradeStates 25 = 298023223876953125
    ∧ fsmGradeStates 25 < fsmGradeStates 26 :=
  ⟨grade_0_states, grade_1_states, grade_25_states, grade_26_excess⟩

/-- ★ **Horizontal axis number-type witness**. -/
theorem horizontal_axis_witness :
    gradeToType 0 = NumberType.natural
    ∧ gradeToType 1 = NumberType.integer
    ∧ gradeToType 5 = NumberType.rational
    ∧ gradeToType 20 = NumberType.algebraic
    ∧ gradeToType 25 = NumberType.highGrade :=
  ⟨grade0_natural, grade1_integer, grade5_rational,
   grade20_algebraic, grade25_substrate⟩

/-- ★ **Grid size witness** — 25 × 25 = 625 cells. -/
theorem grid_size_witness : gridSize = 625 := grid_size_eq_625

/-- ★ **Joint axis index-25 readings** on d=5. -/
theorem index_25_readings_witness :
    levelDim 25 = 33554432
    ∧ fsmGradeStates 25 = 298023223876953125
    ∧ gridSize = 625 := index_25_readings

/-- ★★★ **Total witness** ★★★ — 2D grid: vertical CD level,
    horizontal FSM grade, both read out at index 25, total 625
    cells. -/
theorem total_witness :
    fsmGradeStates 0 = 1
    ∧ fsmGradeStates 25 = 298023223876953125
    ∧ gridSize = 625
    ∧ levelDim 25 = 33554432
    ∧ gradeToType 25 = NumberType.highGrade :=
  ⟨grade_0_states, grade_25_states, grid_size_eq_625,
   rfl, grade25_substrate⟩

end E213.Lib.Math.NumberGrid.Capstone
