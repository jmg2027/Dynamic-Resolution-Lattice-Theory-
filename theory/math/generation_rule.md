# Generation Rule

**Status**: Closed (4 files, capstone `GenerationRule.Capstone`).

## Overview

The **generation rule** defines how 213's structures grow
iteratively: at each step, count the orthogonal direction available,
add the corresponding generator, and iterate.  The result is the
**triangular iteration** that produces the d = 5 vertex set + the
K_{3,2}^{(c=2)} substrate.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/GenerationRule/` (4 files)
- **Capstone**: `GenerationRule.Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `GenerationCount` | Count generators at each step |
| `OrthogonalDirection` | Orthogonal-direction selection |
| `TriangleIteration` | Triangular iteration: step n → step n+1 |
| `GenerationRule.Capstone` | Generation rule master |

## Narrative

Starting from the Raw atom (1 element, 0 axes):
- Step 1: add 1 axis → 2 elements (NT = 2 generated)
- Step 2: orthogonal to step 1 → 3 elements (NS = 3 generated)
- Step 3: NT × NS = 6 cross-elements + d = 5 axial elements
- ...

Each step adds **one orthogonal direction** worth of new
generators.  The triangular structure: total generators at step n
form a triangle number T_n = n(n+1)/2.  At step 5, T_5 = 15 — the
full atomic-vertex inventory of Δ⁴.

This is the 213-native realization of "dimensions emerge by
counting orthogonal directions", made structural.  Companion to
triangular-tower architecture triangular tower (`theory/math/triangular_tower.md`).
