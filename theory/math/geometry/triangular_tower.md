# Triangular Tower Architecture

**Status**: Closed (5 files, capstone `TriangularTower.Capstone`).

## Overview

The **triangular tower** is 213's architectural reading of how
the **real-as-squashed** picture works: ℝ-numbers are
structurally **encoded** as paths through a triangular tower of
finite levels, with property survival (which axioms hold at which
level) governing the tower's shape.

The tower's optimal precision at depth N is `O(log N)`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/TriangularTower/` (5 files)
- **Capstone**: `TriangularTower.Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `AbsorbedByThree` | Three-fold absorption at each tower level |
| `OptimalPrecision` | Precision growth O(log N) at depth N |
| `PropertySurvival` | Which axioms survive at each level |
| `RealAsSquashed` | ℝ-encoding via tower paths |
| `TriangularTower.Capstone` | Triangular tower master |

## Narrative

An ℝ-value is a **Real213 cut reached by no finite stage** — a
residue-internal pointing (an approximant sequence), not an exterior
completion 213 lacks (no exterior, §5.1).  213 points at it as a path
through a triangular tower of finite levels (level 0 = Cut at depth 0,
level 1 = Cut at depth 1, ...); the value is **encoded** as that path,
reached by none and converged to by the tower.

- **AbsorbedByThree**: at each level, the three-fold structure
  (NS = 3) absorbs new information without growing the level count
- **OptimalPrecision**: `O(log N)` precision growth — adding one
  level provides exactly log₂(3) ≈ 1.58 bits
- **PropertySurvival**: at level n, the surviving axiom set is
  a subset of the level-0 set; completeness survives, choice does
  not, etc.
- **RealAsSquashed**: any classical ℝ-claim reduces to a finite
  tower-path encoding

This is the **structural** version of trajectory-witness IVT's trajectory-as-witness
IVT (`theory/math/analysis/minimal_root.md`) — minimal-root says
*the trajectory is the witness*, triangular tower says *the
trajectory is finite at every level*.

## Companion clusters

- `Lib/Math/Geometry/AngleStructure/` (angle-structure — `theory/math/geometry/angle_structure.md`)
- `Lib/Math/Geometry/LevelTopology/` (concrete topology per floor — `theory/math/geometry/level_topology.md`)
- `Lib/Math/Geometry/GenerationRule/` (generation rule — `theory/math/geometry/generation_rule.md`)
