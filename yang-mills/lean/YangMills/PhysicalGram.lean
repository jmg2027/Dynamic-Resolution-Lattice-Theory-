/-
  YangMills/PhysicalGram.lean

  The physical Gram matrix: an invertible 3×3 complex matrix V
  with unit rows (‖V_i‖ = 1).  This encodes three linearly
  independent unit vectors in ℂ³.

  STATUS OF EACH PROPERTY:
    det > 0   — PROVED (from V.det ≠ 0, via normSq)
    det ≤ 1   — PROVED for orthonormal case (det=1)
                 ASSUMED for general case (Hadamard not in Mathlib)

  This file makes the assumption boundary EXPLICIT.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import YangMills.MassGap

set_option autoImplicit false

open Matrix Complex

namespace DRLT.YangMills

/-! ## 1. The Physical Gram Matrix -/

/-- A physical Gram configuration: an invertible matrix with unit rows.
    This is the object that lives on an AAA hinge:
    three unit vectors in ℂ³ forming the spatial sector. -/
structure PhysicalGram where
  /-- The 3×3 complex matrix (rows = spatial vectors) -/
  V : Matrix (Fin 3) (Fin 3) ℂ
  /-- Invertible (linearly independent rows) -/
  det_ne_zero : V.det ≠ 0
  /-- Unit rows: ∑_j |V_{ij}|² = 1 for each row i.
      Physically: each spatial vector has unit norm. -/
  unit_rows : ∀ i : Fin 3, ∑ j : Fin 3, normSq (V i j) = 1

/-! ## 2. DERIVED Properties -/

/-- The Gram determinant |det V|² is strictly positive.
    DERIVED from invertibility (no axiom needed). -/
theorem PhysicalGram.gramDet_pos (g : PhysicalGram) :
    (0 : ℝ) < normSq g.V.det :=
  normSq_pos.mpr g.det_ne_zero

/-- Gram determinant = |det V|² (connecting to GramMatrix.lean) -/
noncomputable def PhysicalGram.gramDet (g : PhysicalGram) : ℝ :=
  normSq g.V.det

/-! ## 3. Conversion to GramAAA -/

/-- Convert a PhysicalGram to GramAAA.

    STATUS:
    - det_pos: PROVED (from invertibility)
    - det_le_one: requires Hadamard's inequality for 3×3 matrices
      with unit rows, which is NOT in Mathlib.

    We take the Hadamard bound as an explicit hypothesis.
    This makes the assumption boundary VISIBLE:
    everything EXCEPT Hadamard is machine-verified. -/
noncomputable def PhysicalGram.toGramAAA (g : PhysicalGram)
    (hadamard : normSq g.V.det ≤ 1) : GramAAA where
  det := normSq g.V.det
  det_pos := g.gramDet_pos
  det_le_one := hadamard

/-! ## 4. The Orthonormal Case (FULLY derived, no assumptions) -/

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The identity matrix has unit rows -/
theorem identity_unit_rows :
    ∀ i : Fin 3, ∑ j : Fin 3, normSq ((1 : Matrix (Fin 3) (Fin 3) ℂ) i j) = 1 := by
  intro i
  simp only [Fin.sum_univ_three]
  fin_cases i <;> simp [Matrix.one_apply, normSq_one, normSq_zero] <;> decide

/-- The identity matrix is invertible -/
theorem identity_det_ne_zero' :
    (1 : Matrix (Fin 3) (Fin 3) ℂ).det ≠ 0 := by simp [det_one]

/-- The orthonormal PhysicalGram -/
def orthonormalGram : PhysicalGram where
  V := 1
  det_ne_zero := identity_det_ne_zero'
  unit_rows := identity_unit_rows

/-- For the orthonormal case, Hadamard is trivially satisfied:
    |det I|² = |1|² = 1 ≤ 1 -/
theorem orthonormal_hadamard :
    normSq orthonormalGram.V.det ≤ 1 := by
  simp [orthonormalGram, det_one, normSq_one]

/-- The orthonormal case gives the ideal GramAAA with det = 1 -/
noncomputable def orthonormalGramAAA : GramAAA :=
  orthonormalGram.toGramAAA orthonormal_hadamard

/-- The mass gap from the orthonormal PhysicalGram equals π -/
theorem mass_gap_orthonormal :
    massGap orthonormalGramAAA = Real.pi := by
  unfold orthonormalGramAAA PhysicalGram.toGramAAA massGap reggeAction hingeArea
  simp [orthonormalGram, det_one, normSq_one, Real.sqrt_one]

/-! ## 5. Assumption Audit

  PROVED (zero assumptions):
  ✓ det(V) ≠ 0           — from LinearIndependent (LinearIndepDet.lean)
  ✓ |det V|² > 0          — from det ≠ 0 (this file)
  ✓ orthonormal: |det|² ≤ 1 — from V = I (this file)
  ✓ Δ > 0                  — from det > 0 (MassGap.lean)
  ✓ Δ = π (orthonormal)    — from det = 1 (this file)

  ASSUMED (one assumption):
  ✗ General Hadamard: normSq(det V) ≤ 1 for any unit-row V
    → needed for: Δ ≤ π (upper bound) for non-orthonormal configs
    → NOT in Mathlib (requires Hadamard's determinant inequality)
    → Passed as explicit `hadamard` parameter in toGramAAA
-/

end DRLT.YangMills
