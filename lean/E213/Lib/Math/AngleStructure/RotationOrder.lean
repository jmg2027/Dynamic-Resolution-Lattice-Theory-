/-!
# Rotation Order at Each CD Level (∅-axiom)

Angle at level n = `360° / order((0, 1))`:

| Level | Rule | order | Angle |
|---|---|---|---|
| 1 | sign | 2 | 180° |
| 2 | complex | 4 | 90° |
| 3+ | quat / oct | 4 (per axis) | 90° |
-/

namespace E213.Lib.Math.AngleStructure.RotationOrder

/-- Canonical rotation order at level n. -/
def levelRotationOrder : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ + 2 => 4

/-- ★ Level 0: trivial (no orthogonal slot). -/
theorem level0 : levelRotationOrder 0 = 1 := rfl

/-- ★ Level 1 sign: order 2 → 180°. -/
theorem level1 : levelRotationOrder 1 = 2 := rfl

/-- ★ Level 2 complex: order 4 → 90°. -/
theorem level2 : levelRotationOrder 2 = 4 := rfl

/-- ★ Per-axis order stable at 4 for n ≥ 2. -/
theorem per_axis_stable (n : Nat) :
    levelRotationOrder (n + 2) = 4 := rfl

/-- Angle in degrees: 360 / rotation order. -/
def angleAtLevel (n : Nat) : Nat := 360 / levelRotationOrder n

/-- ★ Level 0 angle = 360 (trivial). -/
theorem angle_level0 : angleAtLevel 0 = 360 := by
  show 360 / 1 = 360
  rfl

/-- ★ **Level 1 angle = 180°** (negative number = sign flip). -/
theorem angle_level1 : angleAtLevel 1 = 180 := by
  show 360 / 2 = 180
  rfl

/-- ★ **Level 2 angle = 90°** (imaginary i). -/
theorem angle_level2 : angleAtLevel 2 = 90 := by
  show 360 / 4 = 90
  rfl

/-- ★ Levels 3+ per-axis angle = 90°. -/
theorem angle_level3_plus (n : Nat) :
    angleAtLevel (n + 2) = 90 := by
  show 360 / 4 = 90
  rfl

end E213.Lib.Math.AngleStructure.RotationOrder
