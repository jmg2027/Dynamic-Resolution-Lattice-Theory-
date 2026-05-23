# Topology 213

**Status**: Closed (9 files).

Companion to Operation×Topology and LevelTopology chapters.

## Overview

**213-native topology**: open sets are **list-finite covers**,
continuity is **list-preservation** under the cover, compactness
is automatic (every space is list-finite at resolution `N_U`).

A **bare modulus-structure typeclass** unifies the three families
of `Nat → Nat` modulus data living elsewhere in the corpus
(continuity moduli in `Topology/Continuity`, Ricci moduli in
`GeometrizationConjecture/Ricci`, BracketCauchy moduli in
`Analysis/BracketCauchyModulus`) under a single Lean-citable
shape.

This is the topology side of the marathon-completed paradigm
domains (C6 cross-domain unification).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Topology/` (9 files)
- **Umbrella**: `Topology.lean`
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

### Modulus structures: 3-way bridge

Three sub-trees independently arrived at `Nat → Nat` "modulus" data
expressing the schema *target precision ↦ step count*:

- `Topology/Continuity.lean` carries `IsContinuousModulus` with
  `modulus_pos : ∀ k, modulus k ≥ k` (modulus grows monotone with
  target precision).
- `GeometrizationConjecture/Ricci.lean` carries `IsRicciModulus`
  with `anti_monotone` (modulus decreases with target — sharper
  precision needs fewer Ricci-flow steps to be representable).
- `Analysis/BracketCauchyModulus.lean` carries
  `dyadic_bracket_cauchy_modulus` of shape `modulus k = L · k` for
  fixed bracket length `L` (linear with target depth).

`Topology/ModulusStructure.lean` records the shared shape as a bare
typeclass:

```
structure IsModulusStructure : Type where
  modulus : Nat → Nat
```

with `fromContinuous`, `fromRicci`, `fromBracketCauchy` projections
and three canonical instances (`identityModulus`,
`K32RicciModulus`, `bracketCauchyL3`).  The
`three_way_modulus_framework` capstone bundles the three values into
a single Lean-citable identity.

The directional difference (monotone vs anti-monotone vs linear)
is *not* abstracted away — each source-typeclass keeps its own
directional axiom.  The unifying object captures only the shared
`Nat → Nat` data so downstream proofs can reference the common
shape without committing to a directional convention.

This is the 213-native form of the "cross-category functor" question
the parallel raised: rather than constructing an adjunction between
two type-distinct categories (cochain-functions vs Nat→Nat
step-counts), all three instantiate a common bare-data framework.
A full category-theoretic functor would require 213-native `Cat` /
`Functor` infra and is a separate undertaking.

### Connection to other chapters

- `theory/math/operation_topology.md` — operations × topology
- `theory/math/level_topology.md` — per-level topology
- `theory/math/cross_domain_unification.md` (C6) — Topology as a
  paradigm domain instance
- `theory/math/modulus.md` — `HasModulus` / `StrongModulus` family
  in `Lib/Math/Modulus/` (separate sub-tree, same underlying
  Skolem-modulus principle)
- `theory/math/geometrization_conjecture.md` "Open frontier" —
  `IsRicciModulus` source typeclass
