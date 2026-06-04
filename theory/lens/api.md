# Lens Ring API

**Status**: Closed (Lens API + Internal layer).

## Overview

The **Lens public API surface**: the `Lens` type + core
combinators + entry point for files that import Lens.  Also
documents `Lens/Internal/` — proof helpers used by other Lens
sub-clusters but not re-exported.

## Lean source

- `lean/E213/Lens/API.lean` — public surface
- `lean/E213/Lens/Internal/` (4 files) — internal proof helpers
- Companion: `lean/E213/Lens.lean` umbrella (imports all sub-clusters)
- ∅-axiom PURE

## Narrative

The Lens ring (per `lean/E213/ARCHITECTURE.md`) is the **second
ring** of E213 after Term/Theory.  The API surface provides:
- **`Lens`** type definition (function `Raw → α` with a kernel)
- **Composition operators** (`L ∘ M`)
- **Refinement preorder** (`L refines L'`)
- **Universal Lens** entry point

`Lens/API.lean` is the **single-import entry point** for downstream
consumers — most physics + math sub-trees that need Lens machinery
just `import E213.Lens.API`.

`Lens/Internal/` (4 files, no separate INDEX) contains proof
helpers shared across Lens sub-clusters but not exposed to
downstream — kernel-equivalence transitive closure, technical
lemmas, decision procedures.

## Build-time ring ordering

Per `lean/E213/ARCHITECTURE.md`, the Lean tree builds in ring order:
Term → Theory → Lens → Meta → Lib → App.  This is **build
dependency** — what `lake` compiles before what — not a conceptual
ranking.  None of these rings is "below" or "above" another in any
213-sense; the ordering is `import`-resolution only.

The layered-API classification layered-API note

uses OS-stack analogy terms (Kernel / Firmware / Hypervisor /
Application).  Those terms are **expedient names for the build
order**, NOT a claim that Lens "supports" Math/Physics from below.
Per `seed/AXIOM/05_no_exterior.md` §5.1`: there is no exterior;
no ring sits beneath the others as foundation-for-derivation.

The Lens ring is **what distinguishing is**.  Lens application IS
a residue-self-pointing event (per CLAUDE.md "Failure modes
catalog" → "Substrate metaphor" entry).  Not a tool used on Raw
from outside.

## Connection

- `lean/E213/ARCHITECTURE.md` — ring layer canonical
- All other `theory/lens/*` chapters
- Most `theory/math/*` and `theory/physics/*` chapters cite Lens
