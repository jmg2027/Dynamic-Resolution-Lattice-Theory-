# Basel Bound

**Status**: Closed (2 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

The **Basel bound** — finite-rational bracket for `ζ(2) = π²/6`
via the Basel sum `Σ 1/k²`.  Tight two-sided + concrete N=2, 3, 10,
20, 30, 50 brackets.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Basel/` (2 files; consolidated per CONSOLIDATION_PROTOCOL.md)
- **∅-axiom status**: PURE

## Narrative

`S_Basel(N) := Σ_{k=1}^N 1/k²` brackets ζ(2):
`S_Basel(N) ≤ ζ(2) ≤ S_Basel(N) + 1/N`

At N = N_U = 5²⁵, the bracket gap is `~10⁻¹⁸` — far below any
DRLT-observable precision target.

Used in α_em precision derivation: 1/α_em formula uses
`60 · S_Basel(N_U)` as the harmonic base.

## Connection

- `theory/physics/alpha_em/precision_derivation.md` — Basel sum in α_em
- `lean/E213/docs/CONSOLIDATION_PROTOCOL.md` — Basel/Bound consolidation
