# Hyper 213

**Status**: Closed (3 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

213-native handling of "hyper" arithmetic: tetration, Ackermann-style
recursion bounds, very-large-number representation within the
resolution limit `N_U = 5²⁵`.

Establishes the **upper boundary** of 213's representable numbers.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Hyper/` (3 files)
- **∅-axiom status**: PURE

## Narrative

Tetration `a ↑↑ b` and higher hyper-operations exceed `N_U` very
quickly: `2 ↑↑ 5 > N_U`.  Hyper 213 formalizes which hyper-values
are representable + what happens at the boundary:

- `a ↑↑ b ≤ N_U` is decidable for explicit (a, b)
- Beyond `N_U`, the value is **not 213-internal** (per
  `seed/RESOLUTION_LIMIT_SPEC.md`) — only its bracket-class is
  representable

Used downstream as a sanity check: any DRLT observable computation
producing a value `> N_U` indicates a misconfiguration.

## Connection

- `seed/RESOLUTION_LIMIT_SPEC.md` — `N_U` definition
- `theory/math/dyadic_fsm.md` — FSM-based hyper recursion
