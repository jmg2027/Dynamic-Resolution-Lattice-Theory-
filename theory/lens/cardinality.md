# Lens Cardinality

**Status**: Closed (9 files).

## Overview

**Cardinality observables of Raw via Lens.**  Raw is the substrate;
Lens views project Raw → observable space.  Cardinality of Raw and
of Lens-image spaces is the canonical cardinality observable.

Per `seed/RESOLUTION_LIMIT_SPEC.md`: cardinality is a **per-Lens
output**, not a Raw commitment.

## Lean source

- `lean/E213/Lens/Cardinality/` (9 files)
- ∅-axiom PURE

## Narrative

Different Lenses give different cardinalities:
- **count-Lens** at fractal level 2 → `N_U = 5²⁵`
- **leaves-Lens** → count of Raw's leaf-only sub-shapes
- **distinct-Lens** → count of distinguishable Raw equivalence classes
- **bool-Lens** → 2 (per Bool213)

None is "THE cardinality of Raw" — each is a Lens output.  Counterfactual
to ZFC's commitment to "cardinality of a set" as foundational.

## Connection

- `seed/RESOLUTION_LIMIT_SPEC.md` — N_U as count-Lens output
- `theory/lens/universal.md` — universal Lens cardinality
- `theory/lens/properties.md` — cardinality predicates
