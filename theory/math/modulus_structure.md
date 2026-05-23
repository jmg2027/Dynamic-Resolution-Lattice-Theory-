# Modulus Structure — 3-way framework

**Status**: Option-A close (1 file, 12 PURE).
**Promoted from research-notes**: 2026-05-23.

Pattern 1 — typeclass-bridge framework → chapter + archive.

## Overview

Three independent 213 constructions in the analysis / topology /
geometrization branch all carry a `modulus : Nat → Nat` field
expressing "target precision ↦ step count":

  · `IsContinuousModulus` (Topology/Continuity.lean) — cochain
    function with `modulus_pos : ∀ k, modulus k ≥ k` (monotone).
  · `IsRicciModulus` (GeometrizationConjecture/Ricci.lean) — Ricci
    flow modulus with `anti_monotone` (decreasing as target tightens).
  · `dyadic_bracket_cauchy_modulus` (Analysis) — `L · k` linear
    modulus parametrised by bracket length `L`.

`ModulusStructure.lean` introduces a bare `IsModulusStructure`
carrying just `modulus : Nat → Nat`, with explicit projection
functions from each of the three sources.  Records the 3-way
structural parallel as a Lean-formal capstone (Option A close,
deferring the full categorical functor formulation as Option B).

## Lean source

- **File**: `lean/E213/Lib/Math/Topology/ModulusStructure.lean`
- **PURE**: 12 / 0 DIRTY
- **Capstone**: `three_way_modulus_framework` — bundles
  `K32_isRicciModulus`, `identityModulus`, `bracketCauchyL3` as
  three explicit `IsModulusStructure` instances under one type.

## 213-native paradigm parallel

Classical analysis distinguishes ε-δ convergence (analysis),
geometric flow modulus (Ricci), and Cauchy-sequence bracket bounds
(metric theory) as three separate frameworks.

In 213, all three reduce to the **same syntactic object**: a
`Nat → Nat` function annotated with a positional-control
property.  The directional convention (monotone vs anti-monotone)
is the only differentiator; the underlying data type is identical.

`ModulusStructure.lean` records this as: three projections into
one bare type, with no quotient or equivalence-class machinery
needed.  The "framework" IS the typeclass; the projections are
the only computational content.

## Canonical instances

  · `identityModulus : IsModulusStructure` — `modulus = id`.
    The trivial modulus.
  · `K32RicciModulus` — projection of `K32_isRicciModulus`
    (Ricci flow on K_{3,2}^{(c=2)}).
  · `bracketCauchyL3` — `modulus k = 3 · k`, bracket-length-3
    instantiation.

## Connection to other chapters

  · `theory/math/topology.md` — host area; modulus structure
    is one of the analysis-topology bridges.
  · `theory/math/modulus.md` — ε-δ modulus combinators
    (Pattern 1 sibling, also Tier-3 promoted).
  · `theory/math/cauchy.md` — Cauchy-sequence machinery
    (uses bracket-length L parametrisation).
  · `theory/math/geometrization_conjecture.md` — Ricci flow
    derivation (host of `IsRicciModulus`).

## Open frontier — Option B

Option B would lift this to a full categorical formulation:
define morphisms between the three source structures
(`IsContinuousModulus`, `IsRicciModulus`, `bracketCauchy*`) and
prove the 3-way bridge is a functor / adjunction.  The current
Option-A close gives the *typeclass-level* parallel without
committing to a specific morphism formalisation; lifting to
Option B requires (a) defining the category of cochain-function
moduli, (b) defining the category of Nat→Nat moduli, (c)
constructing the functor.  Substantial formalisation effort,
deferred until a downstream theorem requires the functor itself.

## Self-reference

The 3-way bridge IS the 213-native unification.  Classically,
three separate analytic disciplines would require a triangulation
of techniques.  In 213, three constructions are three faces of
one Nat→Nat modulus type; the typeclass IS the unification.  No
external coupling.
