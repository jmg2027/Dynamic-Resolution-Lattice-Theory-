# Bool 213 — Closed-Universe Boolean

**Status**: Closed (2 files).
**Promoted from research-notes**: 2026-05-22.

## Overview

**Raw-encoded Bool**: T and F as specific Raw shapes (Method A:
T = a, F = b — using the two Raw atoms directly).  The catamorphism
`booleanProj := Raw.fold T F and` defines a **Raw-internal projection**
onto the two-element canonical form.

This is the **closed-universe** Bool — every Raw value projects to a
Bool via the foldr, without external Bool type.

## Lean source

- `lean/E213/Lens/Bool213/` (2 files)
- ∅-axiom PURE

## Narrative

Standard Lean Bool is an inductive type external to Raw.  Bool213
is **internal**: T and F are specific Raw shapes, and the projection
`booleanProj : Raw → Raw` (image = {T, F}) is the catamorphism on
the substrate.

Why it matters: any Bool-valued observation in DRLT can be expressed
**without leaving Raw**.  No external Bool type needed; the Raw
itself carries the two-element structure.

## Connection

- `theory/math/logic.md` (Logic 213) — atomic Bool LEM
- `theory/lens/instances.md` — booleanProj as Lens instance
