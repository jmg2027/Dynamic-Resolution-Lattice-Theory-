# Topology 213

**Status**: Closed (7 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).  Companion to Operation×Topology
(G48) and LevelTopology (G49) chapters.

## Overview

**213-native topology**: open sets are **list-finite covers**,
continuity is **list-preservation** under the cover, compactness
is automatic (every space is list-finite at resolution `N_U`).

This is the topology side of the marathon-completed paradigm
domains (C6 cross-domain unification).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Topology/` (7 files)
- **Umbrella**: `Topology.lean`
- **Blueprint**: `blueprints/math/03_topology_213.md` (retired)
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
working level: n = 2, where `configCount 2 = 5²⁵`.  Per G120
Round 3: the level is parametric — not a privileged "resolution
cap" — so compactness holds at every finite level.

### Connection to other chapters

- `theory/math/operation_topology.md` (G48) — operations × topology
- `theory/math/level_topology.md` (G49) — per-level topology
- `theory/math/cross_domain_unification.md` (C6) — Topology as a
  paradigm domain instance
