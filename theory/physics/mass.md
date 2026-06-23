# Mass Hierarchies

**Status**: Closed (3 files).

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

`drlt_no_4th_gen_falsifier` (`Lib/Physics/Simplex/Generations.lean`)
is the structural witness against a 4th fermion generation: it
proves `N_gen = C(NS, NT) = C(3, 2) = 3` — ties to the Simplex
chapter (3-generation structural count).

## Connection

- `theory/physics/foundations.md` — Koide formula
- `theory/physics/simplex.md` — 3-generation structure
- `theory/physics/hadron.md` — quark mass hierarchy
