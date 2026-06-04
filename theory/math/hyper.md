# Hyper 213

**Status**: Closed (3 files).

## Overview

213-native handling of "hyper" arithmetic: tetration, Ackermann-style
recursion bounds, very-large-number representation within the
resolution limit `N_U = 5²⁵`.

Establishes the **upper boundary** of 213's representable numbers.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberSystems/Hyper/` (3 files)
- **∅-axiom status**: PURE

## Narrative

Tetration `a ↑↑ b` and higher hyper-operations exceed
`configCount 2 = 5²⁵` very quickly: `2 ↑↑ 5 > configCount 2`.
Hyper 213 formalizes which hyper-values are representable + what
happens beyond the chosen evaluation level:

- `a ↑↑ b ≤ configCount 2` is decidable for explicit (a, b)
- Beyond `configCount 2`, the value lives at a *different family
  evaluation level* (per N_U re-derivation Round 3 — the resolution boundary is
  a level-choice, not a privileged cap; CLAUDE.md "Universe-constant
  framing" failure mode forbids treating any one value as the
  invariant), and dynamic readings (Pell-Fib, Möbius P^n, ...) do
  not close at the same substrate (per
  `seed/RESOLUTION_LIMIT_SPEC.md`) — only its bracket-class is
  representable

Used downstream as a sanity check: any DRLT observable computation
producing a value `> N_U` indicates a misconfiguration.

## Connection

- `seed/RESOLUTION_LIMIT_SPEC.md` — `N_U` definition
- `theory/math/dyadic_fsm.md` — FSM-based hyper recursion
