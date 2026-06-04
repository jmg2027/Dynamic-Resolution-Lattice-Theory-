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

- **File**: `lean/E213/Lib/Math/Geometry/Topology/ModulusStructure.lean`
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

  · `theory/math/geometry/topology.md` — host area; modulus structure
    is one of the analysis-topology bridges.
  · `theory/math/analysis/modulus.md` — ε-δ modulus combinators (sibling chapter).
  · `theory/math/analysis/cauchy.md` — Cauchy-sequence machinery
    (uses bracket-length L parametrisation).
  · `theory/math/geometry/geometrization_conjecture.md` — Ricci flow
    derivation (host of `IsRicciModulus`).
  · `theory/physics/alpha_em/precision_derivation.md` — α_em
    precision stack; C5 Step 6 hosts `zeta_modulus`.
  · `theory/meta/multiplicity_doctrine.md` Instance 4 — the
    multiplicity-doctrine reading of the 4-way modulus family.

## Option B (categorical functor) — closed (ModulusStructureFunctor.lean, 12 PURE)

`Lib/Math/Geometry/Topology/ModulusStructureFunctor.lean` lifts the Option A
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

## Full adjunction — closed (ModulusStructureAdjunction.lean, 12 PURE)

`Lib/Math/Geometry/Topology/ModulusStructureAdjunction.lean` extends the
Option B functor to a full **adjunction** framework:

  · `ModAdjunction L R` — structure carrying unit `η_m : m → R(L m)`
    and counit `ε_m : L(R m) → m` natural transformations.
  · `idAdjunction : ModAdjunction idF idF` — trivial identity
    adjunction.
  · `shiftBy c` endofunctor: modulus k ↦ m.modulus k + c.
  · `shiftZero_id_adjunction : ModAdjunction (shiftBy 0) idF` —
    shift-zero collapses to identity adjunction (Quot.sound-free
    via pointwise statement).
  · `shiftBy_unit` — for any `c`, unit `m → shiftBy c m` exists
    (trivially: shift adds budget).
  · `shiftBy_counit_bracketCauchy` — for any `c`, counit
    `shiftBy c bracketCauchyL3 → bracketCauchyL3` via the
    reindexing `map k = k + c` (uses `3·k + 3·c ≥ 3·k + c`, i.e.,
    `c ≤ 3·c`).
  · ★★★★★ `modulus_structure_full_adjunction_capstone` bundles
    identity adjunction + shift-zero adjunction + shift-c units +
    shift-c counits at `bracketCauchyL3`.

Reading: the modulus-structure category supports a full adjunction
framework — units / counits between endofunctors `idF` and
`shiftBy c` live as `ModHom` natural transformations.  Non-trivial
shift counits hold at module structures where the modulus growth
dominates the shift (e.g., `bracketCauchyL3` with linear growth
`3·k`).

## Self-reference

The 4-way bridge IS the 213-native unification.  Classically,
four separate analytic disciplines would require a quadrangulation
of techniques.  In 213, four constructions are four faces of
one Nat→Nat modulus type; the typeclass IS the unification.  No
external coupling.
