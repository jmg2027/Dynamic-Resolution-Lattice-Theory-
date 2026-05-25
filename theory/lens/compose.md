# Lens Composition + Refines Preorder

**Status**: Closed (7 files).

## Overview

**How a Lens factors through other Lenses**, and how composition
relates to the `refines` preorder.  Lens composition is the
algebraic structure of "apply Lens A, then apply Lens B to the
output".

## Lean source

- `lean/E213/Lens/Compose/` (7 files)
- ∅-axiom PURE

## Narrative

Two Lenses `L : Raw → α` and `M : α → β` compose to `M ∘ L : Raw → β`.
The composition relates to the `refines` preorder
(`theory/lens/lattice.md`):

```
L refines L'  ↔  ∃ M, L = M ∘ L'
```

(L refines L' iff L can be obtained by post-composing L' with some M).

This makes the Lens-ring into a **category** (objects = Lenses,
morphisms = factor-through), with `refines` as the morphism preorder.

## Connection

- `theory/lens/lattice.md` — refines preorder + lattice
- `theory/lens/universal.md` — initial object in the category
- `theory/lens/unified_equivalence.md` — factor-through IS the
  homomorphism reading of the Lens-arrow (single concept)
