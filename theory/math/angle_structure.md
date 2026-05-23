# Angle Structure

**Status**: Closed (5 files, capstone `G42Capstone`).

## Overview

The **angle-structure programme** identifies which angles are
**Truth** (structural, like 90° at the bipartite split),
**Illusion** (notational artifacts of ZFC squashing, like 180°),
and **Gauge** (free-choice, like 45°).

In 213's discrete substrate, only finitely many angles are
structural; the rest are continuous-extension artifacts.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/AngleStructure/` (5 files)
- **Capstone**: `G42Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `SharedPairSlot` | Shared-pair slot algebra |
| `RotationOrder` | Rotation-order computation |
| `GaugeDiagonal` | Gauge-diagonal structure (45° = free choice) |
| `OrthogonalDoubling` | Orthogonal-doubling step (90° structural) |
| `G42Capstone` | Angle programme master |

## Narrative

In ZFC-style continuous geometry, any angle in [0, 2π) is
"available".  In 213's discrete substrate:

- **90° (orthogonal doubling)** = STRUCTURAL.  The bipartite split
  NS × NT at the K_{3,2}^{(c=2)} substrate forces orthogonality.
- **180° (rotation by π)** = NOTATIONAL ILLUSION.  No primitive
  realization; an artifact of continuous-completion thinking.
- **45° (gauge diagonal)** = GAUGE.  A free choice equivalent under
  the SharedPairSlot equivalence relation.

The capstone proves: every angle assertion in 213-derived geometry
reduces to one of these three readings via the
`SharedPairSlot ∘ RotationOrder ∘ GaugeDiagonal` decomposition.

## Companion clusters

- `Lib/Math/TriangularTower/` (triangular-tower architecture — `theory/math/triangular_tower.md`)
- `Lib/Math/LevelTopology/` (concrete topology per floor — `theory/math/level_topology.md`)
