# `Lib/Math/Geometry/AngleStructure/` — angle / rotation structure

G42 angle-structure programme: shared-pair slot, rotation order,
gauge diagonal, orthogonal doubling.

## Files (7)

  - `SharedPairSlot.lean`       — shared-pair slot algebra
  - `RotationOrder.lean`        — rotation-order computation
  - `GaugeDiagonal.lean`        — gauge-diagonal structure
  - `OrthogonalDoubling.lean`   — orthogonal-doubling step (CD tower, +1 axis/level)
  - `SimplexOrthogonality.lean` — dimension-Lens limit: regular n-simplex `cos = −1/n`
                                  (rational-Gram, no trig), partition-of-unity
                                  dependence, uncentred independence ∀ n
  - `SimplexSelfForm.lean`      — static = dynamic (μF ≅ νF) for the complete-graph
                                  reading: `edgesK (m+1) = edgesK m + m` by `rfl`
                                  (completed-S count = constructive step)
  - `G42Capstone.lean`          — G42 capstone (angle programme master)

## Where to add new files

  - New angle / rotation     → `<Name>.lean`
  - Doubling step            → `<...>Doubling.lean`
  - Capstone                 → `G<N>Capstone`

## Companion clusters

  - `Lib/Math/Geometry/TriangularTower/`  — triangular tower (G47)
  - `Lib/Math/Geometry/LevelTopology/`    — level topology (G49)
