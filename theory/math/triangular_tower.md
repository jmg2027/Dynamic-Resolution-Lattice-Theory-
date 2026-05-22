# Triangular Tower Architecture

**Status**: Closed (5 files, capstone `G47Capstone`).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 — triangular-tower architecture → chapter + archive.

## Overview

The **triangular tower** is 213's architectural reading of how
the **real-as-squashed** picture works: ℝ-numbers are
structurally **encoded** as paths through a triangular tower of
finite levels, with property survival (which axioms hold at which
level) governing the tower's shape.

The tower's optimal precision at depth N is `O(log N)`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/TriangularTower/` (5 files)
- **Capstone**: `G47Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `AbsorbedByThree` | Three-fold absorption at each tower level |
| `OptimalPrecision` | Precision growth O(log N) at depth N |
| `PropertySurvival` | Which axioms survive at each level |
| `RealAsSquashed` | ℝ-encoding via tower paths |
| `G47Capstone` | Triangular tower master |

## Narrative

Classical reals ℝ live "at infinity" — a completion that 213's
substrate doesn't natively have.  But 213 has a triangular tower
of finite levels (level 0 = Cut at depth 0, level 1 = Cut at
depth 1, ...), and any ℝ-value can be **encoded** as a path
through the tower.

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

- `Lib/Math/AngleStructure/` (angle-structure — `theory/math/angle_structure.md`)
- `Lib/Math/LevelTopology/` (concrete topology per floor — `theory/math/level_topology.md`)
- `Lib/Math/GenerationRule/` (generation rule — `theory/math/generation_rule.md`)
