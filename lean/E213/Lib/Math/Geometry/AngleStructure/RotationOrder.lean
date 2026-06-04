/-!
# Rotation Order at Each CD Level (∅-axiom)

Angle at level n = `360° / order((0, 1))`:

| Level | Rule | order | Angle |
|---|---|---|---|
| 1 | sign | 2 | 180° |
| 2 | complex | 4 | 90° |
| 3+ | quat / oct | 4 (per axis) | 90° |
-/

namespace E213.Lib.Math.Geometry.AngleStructure.RotationOrder

/-- Canonical rotation order at level n. -/
def levelRotationOrder : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ + 2 => 4

/-- Angle in degrees: 360 / rotation order. -/
def angleAtLevel (n : Nat) : Nat := 360 / levelRotationOrder n

/-- Level-0 angle: 360°. -/
theorem angle_level0 : angleAtLevel 0 = 360 := rfl

/-- Level-1 angle: 180° (sign). -/
theorem angle_level1 : angleAtLevel 1 = 180 := rfl

/-- Level-2 angle: 90° (complex). -/
theorem angle_level2 : angleAtLevel 2 = 90 := rfl

/-- ★ Rotation-order master — per-level orders and angles.

  level 0: trivial (no orthogonal slot), order = 1, angle = 360°
  level 1: sign, order = 2, angle = 180°
  level 2: complex, order = 4, angle = 90°
  levels ≥ 2: per-axis stable at 4 (angle 90°). -/
theorem rotation_order_master :
    levelRotationOrder 0 = 1
    ∧ levelRotationOrder 1 = 2
    ∧ levelRotationOrder 2 = 4
    ∧ (∀ n : Nat, levelRotationOrder (n + 2) = 4)
    ∧ angleAtLevel 0 = 360
    ∧ angleAtLevel 1 = 180
    ∧ angleAtLevel 2 = 90
    ∧ (∀ n : Nat, angleAtLevel (n + 2) = 90) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · intro _; rfl
  · intro _
    show 360 / 4 = 90
    rfl

end E213.Lib.Math.Geometry.AngleStructure.RotationOrder
