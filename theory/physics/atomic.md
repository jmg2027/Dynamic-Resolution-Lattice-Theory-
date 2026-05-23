# Atomic Physics — Hydrogen / Helium / Screening

**Status**: Closed (21 files, IE sub-cluster).

## Overview

**Atomic-scale physics** observables: hydrogen baseline, helium
extension (electron-electron interaction), screening, bond angles,
ionization energies (IE sub-cluster).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Atomic/` (21 files)
- **Umbrella**: `Atomic.lean`
- **∅-axiom status**: PURE on production critical path

| Group | Files | Topic |
|---|---|---|
| Per-element | `Hydrogen`, `Helium` | Single-element observables |
| Screening | `Screening`, `ScreeningTable` | electron screening |
| Bond | `BondAngles`, ... | bond angle predictions |
| IE/ sub-cluster | ~12 files | per-element ionization energies |

## Narrative

DRLT predicts atomic observables from the (NS, NT, c, d) atomic
substrate without external parameters.  Hydrogen is the baseline
(single electron, single proton); helium adds the
electron-electron interaction; heavier elements add screening
+ bond geometry.

Per atomic-base layer + α_em precision (theory/physics/alpha_em/),
the IE values for H, He, Li, ..., are predicted to ppb-ppm
precision against measured values.

## Connection

- `theory/physics/atomic_base.md` — primitive layer
- `theory/physics/alpha_em/precision_derivation.md` — α_em used in IE
- `theory/physics/couplings.md` — coupling spectrum
