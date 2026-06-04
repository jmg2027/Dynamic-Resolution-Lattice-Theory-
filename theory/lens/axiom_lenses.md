# Axiom Lenses — layered-API classification Tier 4 A2 Endgame

**Status**: Closed (7 files).

## Overview

★★★ **layered-API classification Tier 4 A2 ENDGAME demonstration** ★★★

Lean's external axioms (`propext`, `Quot.sound`, `funext`) are
**not external** to 213 — they are **213-internal Lens choices**
on Raw.  Each axiom corresponds to a specific Lens application
on the Raw substrate.

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

This is the **layered-API classification Tier 4 A2 endgame**: classical foundations
themselves are Lens choices on Raw.

## Connection

- `theory/math/axiom_systems.md` — layered-API classification Tier 5 (the level above this)
- `seed/AXIOM/09_lean_correspondence.md` — R1-R5 judgment game framework
