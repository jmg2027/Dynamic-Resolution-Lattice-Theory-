# Hadron Physics

**Status**: Closed (9 files).

## Overview

Hadronic-scale physics: quark mass hierarchy, proton mass,
neutron-proton mass ratio, proton g-factor, proton-electron mass
ratio.  Includes the m_t/m_c quark-mass chain atomic skeleton sum
(NS·d² + NS·NT² = 87).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Hadron/` (9 files)
- **Umbrella**: `Hadron.lean`
- **∅-axiom status**: PURE

## Narrative

Quark mass ratios in DRLT derive from the atomic primitive layer
via cup-channel decomposition (per α_em precision chapter
machinery).

**m_t/m_c chain skeleton (`MtOverMc.lean`)**: the bare integer
chain sum NS·d² + NS·NT² = 87 from the QuarkHierarchy atomic
factors.  This is the bare skeleton only; it is not 1/α_em = 137
and no underived constant is added to bridge the two.

Proton mass / electron mass = 1836.152... Derived similarly via
cup-channel structure.  Proton g-factor 2.0023 from atomic
substrate Hodge correction.

## Connection

- `theory/physics/atomic_base.md` — primitive substrate
- `theory/physics/alpha_em/precision_derivation.md` — cup-channel machinery
- `catalogs/falsifiers.md` — F25 entry
