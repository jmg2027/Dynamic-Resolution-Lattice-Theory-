import E213.Lib.Math.Geometry.NumberGrid.FSMGradeTaxonomy
import E213.Lib.Math.Geometry.NumberGrid.HorizontalAxis
import E213.Lib.Math.NumberSystems.SignedCut.CD.CDTowerLevel

/-!
# Two-Dimensional Number-System Grid (∅-axiom)

Vertical: CD level `i ∈ {0..25}` (algebraic extension).
Horizontal: FSM grade `j ∈ {0..25}` (pattern-recognizability).
Total: **25 × 25 = 625 cells**.
-/

namespace E213.Lib.Math.Geometry.NumberGrid.TwoDimGrid

open E213.Lib.Math.Geometry.NumberGrid.FSMGradeTaxonomy
  (fsmGradeStates grade_25_states)
open E213.Lib.Math.Geometry.NumberGrid.HorizontalAxis (NumberType gradeToType)
open E213.Lib.Math.NumberSystems.SignedCut.CD.CDTowerLevel (CDLevel levelDim)

/-- Grid cell: pair `(CD level, FSM grade)`. -/
abbrev GridCell := Nat × Nat

/-- Total grid cell count: 25 × 25 = 625. -/
def gridSize : Nat := 25 * 25

/-- ★ Grid is 25×25 = 625. -/
theorem grid_size_eq_625 : gridSize = 625 := rfl

/-- The grade-25 cell `(25, 25)`. -/
def gridCellHighGrade : GridCell := (25, 25)

/-- ★ Cell `(0, 0)` = ℕ at CD level 0 + FSM grade 0. -/
theorem cell_naturals :
    gradeToType 0 = NumberType.natural ∧ levelDim 0 = 1 :=
  ⟨rfl, rfl⟩

/-- ★ Cell `(1, 0)` = ℤ. -/
theorem cell_integers :
    gradeToType 0 = NumberType.natural ∧ levelDim 1 = 2 :=
  ⟨rfl, rfl⟩

/-- ★ Cell `(2, 12)` = ℂ_ℚ at CD level 2 + grade 12. -/
theorem cell_complex_rational :
    gradeToType 12 = NumberType.rational ∧ levelDim 2 = 4 :=
  ⟨rfl, rfl⟩

/-- ★ Cell `(25, 25)` = grade-25 high-grade category. -/
theorem cell_high_grade :
    gradeToType 25 = NumberType.highGrade
    ∧ levelDim 25 = 33554432
    ∧ fsmGradeStates 25 = 298023223876953125 :=
  ⟨rfl, rfl, grade_25_states⟩

/-- ★ **Index-25 readings**: both axis Lens readings at index 25
    (bare arithmetic values). -/
theorem index_25_readings :
    levelDim 25 = 33554432
    ∧ fsmGradeStates 25 = 298023223876953125
    ∧ gridSize = 625 :=
  ⟨rfl, rfl, rfl⟩

end E213.Lib.Math.Geometry.NumberGrid.TwoDimGrid
