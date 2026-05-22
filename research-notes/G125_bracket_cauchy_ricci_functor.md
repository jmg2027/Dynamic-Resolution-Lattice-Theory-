# G125 — BracketCauchy ↔ IsRicciModulus cross-category functor

**Date**: 2026-05-22
**Status**: **OPTION A CLOSE** — typeclass-bridge framework
established via `Topology/ModulusStructure.lean` (12 PURE, single
session)
**Branch**: `claude/g121-open-followup-BCOp3`
**Source**: G123 §3 I-3 residual, `HANDOFF.md` §D

## Close summary (2026-05-22) — Option A

`lean/E213/Lib/Math/Topology/ModulusStructure.lean` (12 PURE):
  · `IsModulusStructure` bare structure (`modulus : Nat → Nat`)
  · `fromContinuous` / `fromRicci` / `fromBracketCauchy` projections
  · Canonical instances: `identityModulus`, `K32RicciModulus`,
    `bracketCauchyL3`
  · `three_way_modulus_framework` capstone bundling all three
    instantiations

Option B (full category theory) deferred — not required for the
3-way structural parallel.

## Why this is a distinct marathon

G123 I-3 closed Ricci-flow ε-Lens integration via the
`IsRicciModulus` structure parallel to `IsContinuousModulus` in
`Topology/Continuity`.  Both are `Nat → Nat` modulus-style
structures with positional-control properties.

The remaining open piece is a **cross-category functor bridge**:
an explicit construction taking `IsRicciModulus` data to
`IsContinuousModulus` data (or vice versa), with adjunction-like
properties that make the parallel formal rather than merely
structural.

## Why this might be ill-posed

The two structures operate on different underlying types:

  · `IsContinuousModulus` carries `f : (Nat → Nat → Bool)
    → (Nat → Nat → Bool)` — a function on cochains.
  · `IsRicciModulus` carries `modulus : Nat → Nat` —
    a step-count function.

These are different *categories*: cochain-functions vs Nat→Nat
modulus functions.  A cross-category functor between them would
require defining the morphisms / objects in each category first,
which is a much larger formalization undertaking.

Concretely:
  · A Ricci-step `k` corresponds to a precision level on the
    cohomology side.  But the cohomology object at step k is a
    cochain function, not a Nat.
  · The functor would need to lift "step counts" to
    "cochain-function refinements" — a non-trivial type-level
    operation.

## Possible resolutions

### Option A — Define both as instances of a common shape

Define a typeclass `IsModulusStructure` capturing the abstract
"modulus + positional control" pattern.  Both `IsContinuousModulus`
and `IsRicciModulus` become instances.  No cross-functor, just
shared abstract framework.

Pros: tractable, ~30 PURE, single-session feasible.
Cons: not a "functor" — just a common abstraction.

### Option B — Define a category of Ricci-flow objects + a category of cochain-function objects, then construct a functor

Pros: genuine cross-category bridge.
Cons: requires category-theoretic infrastructure (Cat, Functor,
NatTrans).  213 doesn't currently have category theory formalized.
Significant infra build-out (~200+ PURE across multiple files).

### Option C — Acknowledge structural parallel only

Pros: honest finding (the parallel is real but cross-category
functor is ill-posed in current 213 infrastructure).
Cons: doesn't close the open item; just documents the obstruction.

## Recommended scope

**Option A**: define `IsModulusStructure` typeclass + instance
proofs.  Bundles both Ricci-modulus and BracketCauchy-modulus as
instances of a common framework.  Adds value without requiring
category theory.

Phase plan:
| Phase | Content | PURE est. |
|---|---|---|
| 1 | `Lib/Math/Topology/ModulusStructure.lean` — abstract typeclass | ~10 |
| 2 | `IsContinuousModulus` ↦ instance | ~5 |
| 3 | `IsRicciModulus` ↦ instance | ~5 |
| 4 | `BracketCauchyModulus` ↦ instance (via the `L * k` formula) | ~10 |
| 5 | Capstone: 3-way instance bundle theorem | ~10 |

Total: ~40 PURE across 1 new file + updates to existing.

Effort: 2-3 sessions.

## Falsifier potential

NONE — pure structural framework.  No measurable prediction.

## Risks

  · Defining the typeclass shape such that all three (Continuous,
    Ricci, BracketCauchy) fit without forcing artificial
    parameterization.
  · Possible scope creep into category theory if Option B is
    pursued.

## Decision point

Before launch, decide: Option A (typeclass) or Option C (document
obstruction).  Option B (full categories) is likely *outside*
G125 scope and would be a separate marathon (e.g., G126: 213-native
category theory infrastructure).
