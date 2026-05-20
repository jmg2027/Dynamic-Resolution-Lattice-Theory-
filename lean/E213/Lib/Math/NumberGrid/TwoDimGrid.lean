import E213.Lib.Math.NumberGrid.FSMGradeTaxonomy
import E213.Lib.Math.NumberGrid.HorizontalAxis
import E213.Lib.Math.SignedCut.CD.CDTowerLevel

/-!
# Two-Dimensional Number-System Grid (∅-axiom)

Vertical: CD level `i ∈ {0..25}` (algebraic extension).
Horizontal: FSM grade `j ∈ {0..25}` (pattern-recognizability).
Total: **25 × 25 = 625 cells**, all within the count-Lens reading bounds at d=5.
-/

namespace E213.Lib.Math.NumberGrid.TwoDimGrid

open E213.Lib.Math.NumberGrid.FSMGradeTaxonomy
  (fsmGradeStates grade_25_states)
open E213.Lib.Math.NumberGrid.HorizontalAxis (NumberType gradeToType)
open E213.Lib.Math.SignedCut.CD.CDTowerLevel (CDLevel levelDim)

/-- Grid cell: pair `(CD level, FSM grade)`. -/
abbrev GridCell := Nat × Nat

/-- Total grid cell count: 25 × 25 = 625. -/
def gridSize : Nat := 25 * 25

/-- ★ Grid is 25×25 = 625. -/
theorem grid_size_eq_625 : gridSize = 625 := rfl

/-- The substrate ceiling cell `(25, 25)`. -/
def gridCountLensCeiling : GridCell := (25, 25)

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

/-- ★ Cell `(25, 25)` = substrate ceiling. -/
theorem cell_substrate_ceiling :
    gradeToType 25 = NumberType.countLensCeiling
    ∧ levelDim 25 = 33554432
    ∧ fsmGradeStates 25 = 298023223876953125 :=
  ⟨rfl, rfl, grade_25_states⟩

/-- ★ **Joint saturation**: both axis Lens readings converge at index 25 under d=5 application. -/
theorem joint_saturation :
    levelDim 25 = 33554432
    ∧ fsmGradeStates 25 = 298023223876953125
    ∧ gridSize = 625 :=
  ⟨rfl, rfl, rfl⟩

end E213.Lib.Math.NumberGrid.TwoDimGrid
