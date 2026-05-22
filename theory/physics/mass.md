# Mass Hierarchies

**Status**: Closed (3 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

Mass hierarchies for fermions: lepton mass ratios (Koide), quark
mass hierarchy, no-fourth-generation falsifier.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Mass/` (3 files)
- **∅-axiom status**: PURE

## Narrative

Lepton mass ratios satisfy the Koide formula:
`(m_e + m_μ + m_τ)² / (√m_e + √m_μ + √m_τ)² = 2/3`

derived from atomic-substrate cup-channel decomposition (per
foundations chapter, Koide section).

`NoFourthGen.lean` is the structural impossibility witness for a
4th fermion generation — ties to Simplex chapter (3-generation
structural count).

## Connection

- `theory/physics/foundations.md` — Koide formula
- `theory/physics/simplex.md` — 3-generation structure
- `theory/physics/hadron.md` — quark mass hierarchy
