# AxiomSystems — layered-API classification Tier 5 Endgame

**Status**: Closed (4 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch; layered-API classification already promoted as a
foundational note remaining at top-level).

## Overview

**layered-API classification Tier 5 (C1-C4) ENDGAME demonstration**: classical foundations
(ZFC, intuitionistic logic, type theory, category theory) are
realized as **Lens compositions on Raw** — not as alternatives to
213, but as Lens-derived views of the same Raw substrate.

This closes the layered-API classification arc at the
**axiom-system level**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/AxiomSystems/` (4 files)
- **∅-axiom status**: PURE

## Narrative

layered-API classification introduced a layered API classification, now generalized to
the build-order ring partition (Term → Theory → Lens → Meta → Lib)
in `lean/E213/ARCHITECTURE.md`.  The "layered" reading there is
**compile-time dependency**, not foundation-vs-derivation.

Tier 5 (the endgame) demonstrates that classical foundations
themselves are Lens compositions:

- **ZFC** = `Set Lens ∘ ChoiceLens ∘ RegularityLens` on Raw
- **Intuitionistic type theory** = `TypeLens ∘ EqualityLens` (no LEM)
- **HoTT** = `PathLens ∘ EquivalenceLens`
- **Topos** = `SheafLens ∘ SubobjectLens`

The C1-C4 demonstrations (4 files) provide explicit Lens
compositions for each axiom system, witnessing that 213's Raw is
**foundational** in the categorical sense (initial object for
Lens-derived foundations).

## Connection

- `research-notes/G12_layered_api_classification.md` (active top-level
  foundational note) — layered API framework
- `theory/math/cross_domain_unification.md` (C6) — extends to
  marathon-completed paradigm domains
