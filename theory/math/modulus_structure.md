# Modulus Structure — 3-way framework

**Status**: Option-A close (1 file, 12 PURE).

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
  · `theory/math/modulus.md` — ε-δ modulus combinators (sibling chapter).
  · `theory/math/cauchy.md` — Cauchy-sequence machinery
    (uses bracket-length L parametrisation).
  · `theory/math/geometrization_conjecture.md` — Ricci flow
    derivation (host of `IsRicciModulus`).

## Option B (categorical functor) — closed (ModulusStructureFunctor.lean, 12 PURE)

`Lib/Math/Topology/ModulusStructureFunctor.lean` lifts the Option A
typeclass parallel to a **category-with-functor** formulation:

  · `ModHom m₁ m₂` — morphism in the category of modulus
    structures.  Carries a Nat-to-Nat reindexing `map` and the
    order-preservation `preserves : ∀ k, m₂(map k) ≥ m₁(k)`.
  · `ModHom.id` / `ModHom.comp` — identity + composition.
  · Category laws at the `map`-projection level: `id_comp`,
    `comp_id`, `comp_assoc` — all `rfl`.
  · Concrete cross-source morphisms:
    - `bracketCauchy_to_ident` (Bracket-Cauchy L=3 → Identity,
      via `map k = 3k`)
    - `ident_to_bracketCauchy_L1` (Identity → Bracket-Cauchy L=1,
      via `map = id`)
  · ★★★★★ `modulus_structure_option_B_capstone` packages the
    morphism existence + category laws + cross-source bridge +
    functor witness.

Reading: the three modulus-source structures from
`Topology.Continuity`, `GeometrizationConjecture.Ricci`, and
bracket-Cauchy moduli are objects in a Lean-formalised category
with `ModHom` arrows, identity, and associative composition.
The functor-level bridge between sources is established;
full adjunction (left / right adjoints between source categories
themselves) requires additional machinery as a follow-up.

## Self-reference

The 3-way bridge IS the 213-native unification.  Classically,
three separate analytic disciplines would require a triangulation
of techniques.  In 213, three constructions are three faces of
one Nat→Nat modulus type; the typeclass IS the unification.  No
external coupling.
