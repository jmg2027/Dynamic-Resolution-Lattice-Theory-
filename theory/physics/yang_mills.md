# Yang-Mills + Weinberg Angle

**Status**: Closed (5 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

Yang-Mills mass gap, SU(5) root structure, W/Z boson masses,
**Weinberg angle** `sin² θ_W`.  Structural identification of the
electroweak sector within the atomic substrate.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/YangMills/` (5 files)
- **Umbrella**: `YangMills.lean`
- **∅-axiom status**: PURE

## Narrative

The electroweak gauge group `SU(2) × U(1)` ⊂ SU(5) GUT decomposes
under the atomic-substrate readings.  `SU5Roots.lean` enumerates
the 24 SU(5) roots; `WMassFalsifier.lean` predicts the W mass to
within experimental bracket.

The Weinberg angle `sin² θ_W = 3/8` (tree-level) emerges as the
ratio of SU(2) generators to SU(2) + U(1) generators in the atomic
substrate; running corrections derived via the coupling-spectrum
machinery (theory/physics/couplings.md).

Yang-Mills mass gap = NS² − 1 = 8 ≠ 0 = the same 8 that is dim H¹(K_{3,2}^{(c=2)})
(the gluon octet).  The mass-gap existence is structural.

## Connection

- `theory/physics/couplings.md` — α_GUT + running
- `theory/physics/symmetry/c3_chain.md` — H¹(K) = 8 = gluon octet
