# Angle Structure

**Status**: Closed (5 files, capstone `AngleStructure.Capstone`).

## Overview

The **angle-structure programme** identifies which angles are
**Truth** (structural, like 90° at the bipartite split),
**Illusion** (notational artifacts with no primitive realization,
like 180°), and **Gauge** (free-choice, like 45°).

Read through 213's distinguishing, only finitely many angles are
structural readings; the rest are continuous-extension artifacts of
a Lens with no primitive realization.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/AngleStructure/` (5 files)
- **Capstone**: `AngleStructure.Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `SharedPairSlot` | Shared-pair slot algebra |
| `RotationOrder` | Rotation-order computation |
| `GaugeDiagonal` | Gauge-diagonal structure (45° = free choice) |
| `OrthogonalDoubling` | Orthogonal-doubling step (90° structural) |
| `AngleStructure.Capstone` | Angle programme master |

## Narrative

A continuous-geometry reading treats every angle in [0, 2π) as
"available".  Read through 213's distinguishing:

- **90° (orthogonal doubling)** = STRUCTURAL.  The bipartite split
  NS × NT at the K_{3,2}^{(c=2)} lattice forces orthogonality.
- **180° (rotation by π)** = NOTATIONAL ILLUSION.  A Lens-artifact
  with no primitive realization (no exterior, §5.1) — an artifact of
  continuous-completion, not a structural angle.
- **45° (gauge diagonal)** = GAUGE.  A free choice equivalent under
  the SharedPairSlot equivalence relation.

The capstone proves: every angle assertion in 213-derived geometry
reduces to one of these three readings via the
`SharedPairSlot ∘ RotationOrder ∘ GaugeDiagonal` decomposition.

## Companion clusters

- `Lib/Math/Geometry/TriangularTower/` (triangular-tower architecture — `theory/math/geometry/triangular_tower.md`)
- `Lib/Math/Geometry/LevelTopology/` (concrete topology per floor — `theory/math/geometry/level_topology.md`)
