# `Lib/Math/Geometry/AngleStructure/` — angle / rotation structure

G42 angle-structure programme: shared-pair slot, rotation order,
gauge diagonal, orthogonal doubling.

## Files (5)

  - `SharedPairSlot.lean`     — shared-pair slot algebra
  - `RotationOrder.lean`      — rotation-order computation
  - `GaugeDiagonal.lean`      — gauge-diagonal structure
  - `OrthogonalDoubling.lean` — orthogonal-doubling step
  - `G42Capstone.lean`        — G42 capstone (angle programme master)

## Where to add new files

  - New angle / rotation     → `<Name>.lean`
  - Doubling step            → `<...>Doubling.lean`
  - Capstone                 → `G<N>Capstone`

## Companion clusters

  - `Lib/Math/Geometry/TriangularTower/`  — triangular tower (G47)
  - `Lib/Math/Geometry/LevelTopology/`    — level topology (G49)
