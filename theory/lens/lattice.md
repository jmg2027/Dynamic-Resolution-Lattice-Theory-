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
- **Bottom** = `idLens` (finest; kernel = Raw equality — collapses nothing)
- **Top** = `constLens` (coarsest; kernel = total, all Raws equivalent — collapses everything)
- **Join** = coarsest Lens refining both
- **Meet** = finest Lens refined by both

`universalLens` is **not** the bottom — it is the per-congruence
normalization map (kernel = the given congruence `E`); see
`theory/lens/universal.md`.

This is the algebraic structure of "available observations" in 213.

## Connection

- `theory/lens/universal.md` — the per-congruence normalization map
  (kernel = `E`; the bottom is `idLens`, not `universalLens`)
- `theory/lens/compose.md` — compose vs refines
- `theory/lens/algebra.md` — kernel theory underlies refines
- `theory/lens/unified_equivalence.md` — `refines` IS the
  Lens-arrow; the lattice is the order on this single concept
