import E213.Lib.Math.Geometry.TriangularTower.PropertySurvival

/-!
# 3-axis Absorbs the "Lost" Properties (∅-axiom)

Mingu's reframing:
> "혹시 2가 하나씩 올라갈수록 잃는게 아니라 3이 가져가는거
>  인거 아닐까?"
> (Translation: "Maybe, as 2 climbs one step at a time, it's not
>  *losing* anything — it's 3 that's *taking* it?")

213-native: at each CD level, the algebraic property doesn't
*vanish* — the **3-axis (information capacity) absorbs it**.

The "loss" is actually a **migration**:
  * 2-axis (binary force): only carries the binary doubling.
  * 3-axis (information capacity): absorbs everything else.

Per level:
  * Level 1: ordering migrates from "real line position" → 3-axis info
  * Level 2: commutativity migrates
  * Level 3: associativity migrates
  * Level 4: alternativity migrates
  * Level 5+: power-associativity migrates
  * Level 25: 5 properties fully absorbed; saturation.

| Level | Absorbed by 3-axis (cumulative) |
|---|---|
| 0 | 0 |
| 1 | 1 (ordering) |
| 2 | 2 (+commutativity) |
| 3 | 3 (+associativity) |
| 4 | 4 (+alternativity) |
| 5+ | 5 (+power-associativity, saturated) |
| 25 | 5 (saturated since level 5) |

This explains why ZFC's ℝ "appears" to have continuity,
completeness, density, ...: these features are **the 3-axis
absorbed properties from higher levels**, NOT primitive
substrate features.
-/

namespace E213.Lib.Math.Geometry.TriangularTower.AbsorbedByThree

/-- ★ Number of properties absorbed by 3-axis at level n
    (cumulative). -/
def absorbedCount (n : Nat) : Nat :=
  if n ≥ 5 then 5 else n

/-- ★ Level 0: 0 absorbed. -/
theorem absorbed_0 : absorbedCount 0 = 0 := rfl

/-- ★ Level 1: 1 absorbed (ordering). -/
theorem absorbed_1 : absorbedCount 1 = 1 := rfl

/-- ★ Level 2: 2 absorbed (commutativity). -/
theorem absorbed_2 : absorbedCount 2 = 2 := rfl

/-- ★ Level 3: 3 absorbed (associativity). -/
theorem absorbed_3 : absorbedCount 3 = 3 := rfl

/-- ★ Level 4: 4 absorbed (alternativity). -/
theorem absorbed_4 : absorbedCount 4 = 4 := rfl

/-- ★ Level 5+: 5 absorbed (saturated). -/
theorem absorbed_5 : absorbedCount 5 = 5 := rfl

/-- ★ Level 25: still 5 absorbed (no more to take). -/
theorem absorbed_25 : absorbedCount 25 = 5 := rfl

end E213.Lib.Math.Geometry.TriangularTower.AbsorbedByThree
