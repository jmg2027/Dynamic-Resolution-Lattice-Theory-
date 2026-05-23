import E213.Lib.Math.SignedCut.CD.CDTowerLevel

/-!
# Orthogonal Axis Doubling — The Mechanical 90° Extension (∅-axiom)

Mingu's elaboration (part 3):

> "Cayley-Dickson 타워를 한 층 올라갈 때마다 벌어지는 일은,
>  기존의 공간 전체에 대해 새롭게 90도로 직교하는 축을 기계적으로
>  하나 더 세우는 작업 그 이상도 이하도 아닙니다."

Each CD level doubles the dimension by adding ONE 90°-orthogonal
axis to the existing space:

  * Level 0: 1D Cut (positive magnitude only)
  * Level 1: 2D plane (Cut × Cut) — adds 1 orthogonal axis
  * Level 2: 4D space — adds 1 more orthogonal axis
  * Level 3: 8D — adds 1 more
  * ...
  * Level 25: `2^25 ≈ 3.4·10⁷` orthogonal axes

ZFC squashes intermediate levels via "gauge projection":
  * Level 1's 2D → 1D ℝ (squashes Pos/Neg diagonal)
  * Level 2's 4D → 2D ℂ (squashes signed-imaginary diagonal)
  * etc.

213-native: NO squashing.  All `2^n` axes are kept genuinely
orthogonal at the substrate level.
-/

namespace E213.Lib.Math.AngleStructure.OrthogonalDoubling

open E213.Lib.Math.SignedCut.CD.CDTowerLevel (levelDim)

/-- ★ **Dimension doubling at each level** (= `2^n`). -/
theorem dim_doubling : ∀ n,
    levelDim (n + 1) = 2 * levelDim n
  | _ => rfl

/-- ★ **Concrete dimensions through level 5**. -/
theorem concrete_dims :
    levelDim 0 = 1
    ∧ levelDim 1 = 2
    ∧ levelDim 2 = 4
    ∧ levelDim 3 = 8
    ∧ levelDim 4 = 16
    ∧ levelDim 5 = 32 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **Level 25 has 2²⁵ orthogonal axes** = 33,554,432. -/
theorem level25_orthogonal_axes : levelDim 25 = 33554432 := rfl

/-- ★ **Number of "imaginary" axes at level n** = `2^n − 1`
    (subtract 1 for the "real" axis). -/
def imaginaryAxesAtLevel (n : Nat) : Nat := levelDim n - 1

/-- ★ Level 1 has 1 "imaginary" axis (the negative axis). -/
theorem level1_imaginaries :
    imaginaryAxesAtLevel 1 = 1 := rfl

/-- ★ Level 2 has 3 imaginary axes (i + signed-extension axes). -/
theorem level2_imaginaries :
    imaginaryAxesAtLevel 2 = 3 := rfl

/-- ★ Level 3 has 7 imaginaries (i, j, k + 4 more from signed). -/
theorem level3_imaginaries :
    imaginaryAxesAtLevel 3 = 7 := rfl

/-- ★ Level 25 has 2²⁵ − 1 = 33554431 imaginary axes. -/
theorem level25_imaginaries :
    imaginaryAxesAtLevel 25 = 33554431 := rfl

end E213.Lib.Math.AngleStructure.OrthogonalDoubling
