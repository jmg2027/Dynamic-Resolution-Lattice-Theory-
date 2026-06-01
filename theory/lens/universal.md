# Universal Lens (G1 anchor)

**Status**: Closed (13 files).

## Overview

**Construction of the universal Lens** — the canonical Lens whose
view is **injective** (no distinct Raws collapsed).  Gives the
canonical-form equivalence relation on Lenses.

This is the **G1 anchor** — universal-lens unification.

## Lean source

- `lean/E213/Lens/Universal/` (13 files)
- ∅-axiom PURE

## Narrative

Every Lens collapses some Raws (its kernel).  The **universal Lens**
is the one that collapses nothing (kernel = identity).  Its existence
is the structural realization of "Raw is observable in its entirety"
— per G1.

The 13 files cover:
- **Construction**: explicit `universalLens : Raw → Tree (Bool ⊕ Bool)`
- **Injectivity**: proof that universalLens doesn't collapse any Raws
- **Universality**: every other Lens factors through universalLens
- **Equivalence on Lenses**: two Lenses are equivalent iff they have
  the same kernel iff they factor universalLens identically

This makes the Lens ring into a **category with initial object** —
the universalLens is the initial Lens.

## Connection

- `research-notes/G1_universal_lens.md` (active foundational note)
- `theory/lens/algebra.md` — kernel theory
- `theory/lens/lattice.md` — universal = bottom of lattice
- `theory/lens/compose.md` — factor-through definition
- `theory/lens/unified_equivalence.md` — universalLens realises
  the slash-congruence → Lens-kernel direction of the single
  concept.  Its `=`-form (`universalLens_kernel_eq_E`) is sealed
  category (b); the distinguishing `equivR`-form
  (`universalLens_kernel_eq_E_R`) is PURE
  (`theory/lens/dirty_recovery_patterns.md` Pattern P5).
