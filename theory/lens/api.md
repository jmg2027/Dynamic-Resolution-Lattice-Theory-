# Lens Ring API

**Status**: Closed (Lens API + Internal layer).
**Promoted from research-notes**: 2026-05-22.

## Overview

The **Lens ring public API surface**: the `Lens` type + core
combinators + entry point for downstream consumers.  Also documents
the `Lens/Internal/` proof infrastructure (private to Lens layer).

## Lean source

- `lean/E213/Lens/API.lean` — public surface
- `lean/E213/Lens/Internal/` (4 files) — internal proof infrastructure
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

`Lens/Internal/` (4 files, no separate INDEX) contains the proof
infrastructure shared across Lens sub-clusters but not exposed to
downstream — kernel-equivalence transitive closure, technical
lemmas, decision procedures.

## Layered API classification

Per G12 layered API classification (still active in
`research-notes/G12_layered_api_classification.md`):
- **L1 (Kernel)**: Term + Theory rings (Raw, base axiom)
- **L2 (Firmware)**: Lens ring (this chapter's scope)
- **L3 (Hypervisor)**: Meta ring (reflective primitives)
- **L4 (Application)**: Lib + App rings (Math + Physics + executables)

The Lens ring is **the** structural intermediate layer: what makes
Raw observable.

## Connection

- `research-notes/G12_layered_api_classification.md` (active)
- `lean/E213/ARCHITECTURE.md` — ring layer canonical
- All other `theory/lens/*` chapters
- Most `theory/math/*` and `theory/physics/*` chapters cite Lens
