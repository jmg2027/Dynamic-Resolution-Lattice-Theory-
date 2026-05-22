# Hadron Physics

**Status**: Closed (9 files; F25 m_t/m_c falsifier).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

Hadronic-scale physics: quark mass hierarchy, proton mass,
neutron-proton mass ratio, proton g-factor, proton-electron mass
ratio.  Includes **F25 falsifier**: `m_t / m_c ≈ 137 ∈ [130, 145]`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Hadron/` (9 files)
- **Umbrella**: `Hadron.lean`
- **∅-axiom status**: PURE

## Narrative

Quark mass ratios in DRLT derive from the atomic primitive layer
via cup-channel decomposition (per α_em precision chapter
machinery).

**F25 falsifier (`MtOverMc.lean`)**: m_t / m_c ratio brackets to
[130, 145] from DRLT structure.  Measured value ~137 sits in this
bracket.  Measured ratio outside [130, 145] would falsify.

Proton mass / electron mass = 1836.152... Derived similarly via
cup-channel structure.  Proton g-factor 2.0023 from atomic
substrate Hodge correction.

## Connection

- `theory/physics/atomic_base.md` — primitive substrate
- `theory/physics/alpha_em/precision_derivation.md` — cup-channel machinery
- `catalogs/falsifiers.md` — F25 entry
