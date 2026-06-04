# `Lib/Math/Geometry/LevelTopology/` — level-structure topology

Topological structure of the Cayley-Dickson level tower
(complex / quaternion / sign / magnitude topology) + G49 capstone.

## Files (6)

  - `ComplexTopology.lean`         — level-2 (ℂ-like) topology
  - `QuaternionTopology.lean`      — level-3 (quaternion-like) topology
  - `SignTopology.lean`            — sign-structure topology
  - `MagnitudeTopology.lean`       — magnitude-structure topology
  - `TwoTowersDivergence.lean`     — two-tower divergence theorem
  - `G49Capstone.lean`             — G49 capstone (level-topology master)

## Where to add new files

  - New level-topology variant   → `<Level>Topology.lean`
  - Tower divergence / fixpoint  → `<...>TowersDivergence` /
                                    `<...>TowerFixedPoint`
  - Capstone                     → `G<N>Capstone`

## Companion clusters

  - `Lib/Math/Geometry/Topology/`             — base topology primitives
  - `Lib/Math/CayleyDickson/Tower/`  — level tower machinery
  - `Lib/Math/Geometry/OperationTopology/`    — operation-level topology
