# Axiom Lenses — Lean's `propext` / `Quot.sound` / `funext` as Raw-internal Lens choices

**Status**: Closed (7 files).

## Overview

Lean's external axioms (`propext`, `Quot.sound`, `funext`) are
**not external** to 213 — they are **213-internal Lens choices** on
Raw.  Each corresponds to a specific Lens application; applying it is
an operational choice, not a foundational necessity.

## Lean source

- `lean/E213/Lens/AxiomLenses/` (7 files)
- ∅-axiom PURE (the chapter's own theorems; the demonstrated
  "axioms-as-lenses" are tagged as sealed-by-design when used)

## Narrative

Classical Lean treats `propext`, `Quot.sound`, `funext`
as foundational axioms outside the type theory.  213's reading:
each is a **specific Lens** that the user can choose to apply or
not:

- **propext** = `PropExtensionalityLens` (collapses propositionally-
  equivalent props)
- **Quot.sound** = `QuotientSoundnessLens` (collapses quotient
  representatives)
- **funext** = `FunctionExtensionalityLens` (collapses
  point-wise-equal functions)

213 doesn't apply these by default → DRLT theorems are
PURE.  Other Lean libraries that DO apply them are using
those Lenses, but the choice is operational, not foundational.
So the classical/constructive split is itself a Lens choice on Raw,
not a wall between two foundations.

## Connection

- `theory/math/foundations/axiom_systems.md` — classical axiom-system
  *fragments* as Lens readings on Raw
- `seed/AXIOM/09_lean_correspondence.md` — the faithful Lean emulator;
  `seed/AXIOM/10_encoding_costs.md` §10.2 on why `Quot.sound` is banned
  by the ∅-axiom contract
