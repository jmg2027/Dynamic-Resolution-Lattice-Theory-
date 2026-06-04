# Level Topology

**Status**: Closed (6 files, capstone `LevelTopology.Capstone`).

## Overview

The **level topology** assigns each Cayley-Dickson level a
**distinct topology type**: sign at L0, magnitude at L1, complex
at L2, quaternion at L3, ...  The tower of topologies diverges
under composition — two paths through the tower can land on
**different** topologies even from the same starting level.

This is the topological-side counterpart to the algebra tower
(`theory/math/cayley_dickson/algebra_tower.md`).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/LevelTopology/` (6 files)
- **Capstone**: `LevelTopology.Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `SignTopology` | L0 sign topology (1 bit) |
| `MagnitudeTopology` | L1 magnitude topology (signed magnitude) |
| `ComplexTopology` | L2 complex topology (re, im) |
| `QuaternionTopology` | L3 quaternion topology (1, i, j, k) |
| `TwoTowersDivergence` | Two paths diverge to different topologies |
| `LevelTopology.Capstone` | Level topology master |

## Narrative

The Cayley-Dickson tower (`Lib/Math/Algebra/CayleyDickson/Tower/`) grows
algebraic structure at each level.  The **topological** side does
the same:

```
L0: sign topology         (sign: +/−, discrete)
L1: magnitude topology    (|x|: non-negative, ordered)
L2: complex topology      (x, y): pair, planar)
L3: quaternion topology   ((x, y, z, w): 4-tuple, spherical)
L4: octonion topology     (8-tuple, hyperspherical)
...
```

Each level's topology is **structural** — not a chosen metric, but
the discrete Lens output of the CD-doubling step.  At L2, the
"complex topology" is literally pair-of-magnitudes, not a metric
imposed externally.

**TwoTowersDivergence**: two paths through the tower (e.g.,
"left-double then right-double" vs "right-double then left-double")
can produce different topologies, even at the same level.  This is
the non-commutativity of the CD-doubling functor, made
topological.

## Companion clusters

- `Lib/Math/Algebra/CayleyDickson/Tower/` (algebra tower, `theory/math/cayley_dickson/algebra_tower.md`)
- `Lib/Math/Geometry/AngleStructure/` (angle-structure — `theory/math/geometry/angle_structure.md`)
- `Lib/Math/Geometry/TriangularTower/` (triangular-tower architecture — `theory/math/geometry/triangular_tower.md`)
