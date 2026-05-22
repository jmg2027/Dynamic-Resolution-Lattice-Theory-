# Geometry — Algebraic + Rotation

**Status**: Closed (2 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

213-native geometry primitives: algebraic geometry (cross-link to
HodgeConjecture and universe_chain) + rotation geometry (companion
to AngleStructure G42).

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
or `Lens/Number/Nat213/AlgebraicGeometry.lean` (universe-chain).

`Rotation.lean` provides 213-native rotation operations
(angle = Lens-output structural angle per G42 angle_structure
chapter).

## Connection

- `theory/math/cohomology/hodge_conjecture.md` — algebraic-geometric core
- `theory/math/universe_chain.md` — algebraic_geometric_core
- `theory/math/angle_structure.md` — rotation order
