# Lens Properties — Predicates About Lenses

**Status**: Closed (21 files).

## Overview

**Predicates about a Lens** (is it a leaf? Canonical? Does it
have A-B refinement? ...) and the theorems characterising them.

The "meta-Lens" layer: Lenses about Lenses.

## Lean source

- `lean/E213/Lens/Properties/` (21 files)
- ∅-axiom PURE

## Narrative

Important Lens predicates:
- **IsLeafLens** — Lens whose image is a "leaf" (irreducible)
- **IsCanonicalLens** — Lens equivalent to its canonical form
- **HasABRefinement** — Lens has a refinement into A-only / B-only parts
- **IsInjective** — Lens that doesn't collapse Raws (= universal Lens iff total)
- **IsLevel<N>Lens** — Lens at fractal level N
- **IsFinitePartition** — Lens whose kernel has finitely many classes
- **IsCardinalityLens** — Lens whose output is a count

Each predicate has decidability witnesses + characterization theorems.

## Connection

- `theory/lens/universal.md` — IsInjective ↔ universal
- `theory/lens/cardinality.md` — IsCardinalityLens instances
- `theory/lens/instances.md` — concrete Lenses tagged by these predicates
