# Lens Lattice — Refines Preorder

**Status**: Closed (9 files).

## Overview

**`Lens.refines` preorder + lattice structure (join / meet).**
The set of all Lenses on Raw forms a lattice under the refines
preorder; join = "Lens that distinguishes whatever either Lens
distinguishes"; meet = "Lens that collapses whatever either
Lens collapses".

## Lean source

- `lean/E213/Lens/Lattice/` (9 files)
- ∅-axiom PURE

## Narrative

`L refines L'` means L distinguishes at least everything L' does.
Equivalently: L's kernel is finer than L''s.

The Lens lattice has:
- **Top** = trivial Lens (all Raws equivalent, kernel = Raw × Raw)
- **Bottom** = universal Lens (no collapse, kernel = id)
- **Join** = coarsest Lens refining both
- **Meet** = finest Lens refined by both

This is the algebraic structure of "available observations" in 213.

## Connection

- `theory/lens/universal.md` — bottom of the lattice
- `theory/lens/compose.md` — compose vs refines
- `theory/lens/algebra.md` — kernel theory underlies refines
