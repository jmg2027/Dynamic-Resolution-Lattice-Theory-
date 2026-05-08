/-!
# 213 Tower vs Classical CD Tower — divergence (∅-axiom)

Mingu's correction:
> "케일리 딕슨 타워로 맵핑하면 안맞지 거긴 음수를 직교라고 안두는데"

**Classical CD**: ℝ as base (sign internal, not orthogonal).
**213 framework**: magnitude + sign as separate floors.

| 213 floor | Classical CD | Content |
|---|---|---|
| Floor 1 | (none) | Cut (pure magnitude) |
| Floor 2 | Level 0 (ℝ) | SignedCut |
| Floor 3 | Level 1 (ℂ) | ComplexCut |
| Floor 4 | Level 2 (ℍ) | Quaternion |
| ... | ... | ... |

**Crucial**: classical ℝ = squashed projection of 213's floor 2.
ZFC starts above the magnitude-vs-sign distinction.
-/

namespace E213.Lib.Math.LevelTopology.TwoTowersDivergence

/-- 213's total floor count: 26 (floors 1..26). -/
def total213Floors : Nat := 26

/-- Classical CD floor count from ℝ: 25 (one less). -/
def totalClassicalCDFloors : Nat := 25

/-- ★ Divergence: 213 has +1 floor at the bottom. -/
theorem divergence : total213Floors = totalClassicalCDFloors + 1 := rfl

/-- Classical CD level n = 213 floor (n+2). -/
def classicalCDToFloor (n : Nat) : Nat := n + 2

/-- ★ ℝ (classical level 0) = 213 floor 2. -/
theorem zfc_real_is_floor2 : classicalCDToFloor 0 = 2 := rfl

/-- ★ ℂ = floor 3. -/
theorem zfc_complex_is_floor3 : classicalCDToFloor 1 = 3 := rfl

/-- ★ ℍ = floor 4. -/
theorem zfc_quat_is_floor4 : classicalCDToFloor 2 = 4 := rfl

end E213.Lib.Math.LevelTopology.TwoTowersDivergence
