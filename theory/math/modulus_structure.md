# Modulus Structure — 4-way framework

**Status**: Option-A close (1 file, 16 PURE).

## Overview

Four independent 213 constructions across the analysis /
topology / geometrization / physics branches all carry a
`modulus : Nat → Nat` field expressing "target precision ↦ step
count":

  · `IsContinuousModulus` (Topology/Continuity.lean) — cochain
    function with `modulus_pos : ∀ k, modulus k ≥ k` (monotone).
  · `IsRicciModulus` (GeometrizationConjecture/Ricci.lean) — Ricci
    flow modulus with `anti_monotone` (decreasing as target tightens).
  · `dyadic_bracket_cauchy_modulus` (Analysis) — `L · k` linear
    modulus parametrised by bracket length `L`.
  · `zeta_modulus : DepthModulus` (Physics/AlphaEM/FractalLevelZetaModulus.lean) —
    identity `N ↦ N` (1 bit per fractal step), discretising the
    ζ_K^(L) → ζ(2) convergence in the α_em precision-derivation
    stack (C5 Step 6).

`ModulusStructure.lean` introduces a bare `IsModulusStructure`
carrying just `modulus : Nat → Nat`, with explicit projection
functions from each of the four sources.  Records the 4-way
structural parallel as a Lean-formal capstone (Option A close,
deferring the full categorical functor formulation as Option B).

## Lean source

- **File**: `lean/E213/Lib/Math/Topology/ModulusStructure.lean`
- **PURE**: 16 / 0 DIRTY
- **Capstones**:
  - `three_way_modulus_framework` — original 3-way bundle.
  - `four_way_modulus_framework` — extended bundle that adds the
    AlphaEM `zetaModulusStructure` instance, crossing the
    Math/Physics directory boundary without changing the
    framework.

## 213-native paradigm parallel

Classical analysis distinguishes ε-δ convergence (analysis),
geometric flow modulus (Ricci), Cauchy-sequence bracket bounds
(metric theory), and the spectral / zeta-precision modulus
(number theory side of physics constant derivation) as separate
frameworks.

In 213, all four reduce to the **same syntactic object**: a
`Nat → Nat` function annotated with a positional-control
property.  The directional convention (monotone vs anti-monotone)
is the only differentiator; the underlying data type is identical.

`ModulusStructure.lean` records this as: four projections into
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
  · `zetaModulusStructure` — projection of `zeta_modulus`
    (`fun N => N`), α_em fractal-level ζ-convergence (C5 Step 6).

## Connection to other chapters

  · `theory/math/topology.md` — host area; modulus structure
    is one of the analysis-topology bridges.
  · `theory/math/modulus.md` — ε-δ modulus combinators (sibling chapter).
  · `theory/math/cauchy.md` — Cauchy-sequence machinery
    (uses bracket-length L parametrisation).
  · `theory/math/geometrization_conjecture.md` — Ricci flow
    derivation (host of `IsRicciModulus`).
  · `theory/physics/alpha_em/precision_derivation.md` — α_em
    precision stack; C5 Step 6 hosts `zeta_modulus`.
  · `theory/meta/multiplicity_doctrine.md` Instance 4 — the
    multiplicity-doctrine reading of the 4-way modulus family.

## Open frontier — Option B

Option B would lift this to a full categorical formulation:
define morphisms between the four source structures
(`IsContinuousModulus`, `IsRicciModulus`, `bracketCauchy*`,
`zeta_modulus`) and prove the 4-way bridge is a functor /
adjunction.  The current Option-A close gives the *typeclass-level*
parallel without committing to a specific morphism formalisation;
lifting to Option B requires (a) defining the category of
cochain-function moduli, (b) defining the category of Nat→Nat
moduli, (c) constructing the functor.  Substantial formalisation
effort, deferred until a downstream theorem requires the functor
itself.

## Self-reference

The 4-way bridge IS the 213-native unification.  Classically,
four separate analytic disciplines would require a quadrangulation
of techniques.  In 213, four constructions are four faces of
one Nat→Nat modulus type; the typeclass IS the unification.  No
external coupling.
