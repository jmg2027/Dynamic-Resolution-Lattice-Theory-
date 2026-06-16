# Geometry — Algebraic + Rotation

**Status**: Closed (2 files).

## Overview

213-native geometry primitives: algebraic geometry (cross-link to
HodgeConjecture and universe_chain) + rotation geometry (companion
to AngleStructure angle-structure).

## Lean source

- `lean/E213/Lib/Math/Geometry/` (2 files)
- ∅-axiom PURE

| File | Purpose |
|---|---|
| `AlgebraicGeometry` | High-level algebraic-geometry primitives + bridges |
| `Rotation` | Rotation operations on 213-native coordinates |

## Narrative

`AlgebraicGeometry.lean` is a thin bridge layer — most algebraic
geometry content lives in `Lib/Math/Cohomology/HodgeConjecture/`
or `Lib/Math/Geometry/AlgebraicGeometry.lean` (universe-chain).

`Rotation.lean` provides 213-native rotation operations
(angle = Lens-output structural angle per angle-structure angle_structure
chapter).

## Connection

- `theory/math/cohomology/hodge.md` — algebraic-geometric core
- `theory/math/foundations/universe_chain.md` — algebraic_geometric_core
- `theory/math/geometry/angle_structure.md` — rotation order
