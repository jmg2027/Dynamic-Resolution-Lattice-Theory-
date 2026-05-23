# Lens Number Systems

**Status**: Closed (17 files; Nat213 sub-tree covered in universe_chain).

## Overview

**Raw-derived number systems**: each module is a `Raw.fold`
catamorphism output reified as a number system.  Per
`lean/E213/ARCHITECTURE.md`: **catamorphism + data choice =
Lens-layer artifact**.

## Lean source

- `lean/E213/Lens/Number/` (17 files including `Nat213/` sub-tree)
- ∅-axiom PURE

## Narrative

Different `Raw.fold` choices yield different number systems:
- **Nat213** (`Nat213/`) = (NS-spatial + NT-temporal) constructor counts → ℕ-like
- **Int213** = signed extension via SignedCut-style pair
- **Other Lens.Number** instances: rational, dyadic, ...

`Nat213/` sub-tree (12 files) is **fully covered** in
`theory/math/universe_chain.md` — atomicity → Möbius → CRT chapter.
This Lens-side chapter is for the **classification frame**: number
systems as Lens-layer artifacts, not Theory-layer foundations.

## Connection

- `theory/math/universe_chain.md` — Nat213 sub-tree narrative
- `lean/E213/ARCHITECTURE.md` — catamorphism = Lens artifact
- `theory/lens/algebra.md` — kernel underlies catamorphism choice
