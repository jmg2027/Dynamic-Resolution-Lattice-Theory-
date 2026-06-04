# Topology 213

**Status**: Closed (8 modules + `Topology.lean` umbrella).

Companion to Operation×Topology and LevelTopology chapters.

## Overview

**213-native topology**: open sets are **list-finite covers**,
continuity is **list-preservation** under the cover, compactness
is automatic (every space is list-finite at resolution `N_U`).

This is the topology side of the closed paradigm domains (C6
cross-domain unification).  The `IsModulusStructure` typeclass
bridge (Continuity / Ricci / BracketCauchy) lives here as a
sibling module; its dedicated narrative is
`theory/math/modulus_structure.md`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/Topology/` (8 modules)
- **Umbrella**: `lean/E213/Lib/Math/Geometry/Topology.lean`
- **∅-axiom status**: PURE

## Narrative

### List-finite covers

Classical topology has uncountable open sets (the real line has a
continuum of open intervals).  In 213's substrate, every open set
is **list-finite** at the resolution `N_U`:

```
Open213 X := { cover : List (Set X) // every element is open + cover is finite }
```

Continuity becomes:

```
Continuous f := preimage of any list-finite cover is list-finite
```

Compactness is automatic: every Set X readable at fractal level n
(via the parametric family `configCount`) has `≤ configCount n`
elements, so any cover restricts to a finite sub-cover.  Common
working level: n = 2, where `configCount 2 = 5²⁵`.  Per N_U re-derivation
Round 3: the level is parametric — not a privileged "resolution
cap" — so compactness holds at every finite level.

### Modulus structures

`Topology/ModulusStructure.lean` adds a bare `IsModulusStructure`
typeclass that unifies three sub-tree-local `Nat → Nat` modulus
families (`IsContinuousModulus`, `IsRicciModulus`,
`BracketCauchyModulus`) under one Lean-citable shape.  Full
narrative + cross-frame discussion: `theory/math/modulus_structure.md`.

### Connection to other chapters

- `theory/math/operation_topology.md` — operations × topology
- `theory/math/level_topology.md` — per-level topology
- `theory/math/cross_domain_unification.md` (C6) — Topology as a
  paradigm domain instance
- `theory/math/modulus.md` — `HasModulus` / `StrongModulus` family
  in `Lib/Math/Analysis/Modulus/` (separate sub-tree, same underlying
  Skolem-modulus principle)
- `theory/math/geometrization_conjecture.md` "Open frontier" —
  `IsRicciModulus` source typeclass
