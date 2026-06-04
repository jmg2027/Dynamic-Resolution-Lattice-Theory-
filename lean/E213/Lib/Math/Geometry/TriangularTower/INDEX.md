# `Lib/Math/Geometry/TriangularTower/` — triangular tower structure

G47 triangular-tower programme: Real-as-squashed encoding, property
survival across squash, optimal precision, "absorbed by three"
characterisation.

## Files (5)

  - `RealAsSquashed.lean`     — Real-as-squashed encoding
  - `PropertySurvival.lean`   — properties surviving the squash
  - `OptimalPrecision.lean`   — optimal-precision result
  - `AbsorbedByThree.lean`    — "absorbed by three" theorem
  - `G47Capstone.lean`        — G47 capstone (TT programme master)

## Where to add new files

  - Squash construction step    → `Real<...>Squashed.lean`
  - Survival lemma              → `<Property>Survival.lean`
  - Precision refinement        → `<...>Precision.lean`
  - Capstone                    → `G<N>Capstone.lean`

## Companion clusters

  - `Lib/Math/Algebra/CayleyDickson/Tower/` — CD tower (different topic, both
                                       "tower" pattern)
  - `Lib/Math/Geometry/LevelTopology/`       — level topology
