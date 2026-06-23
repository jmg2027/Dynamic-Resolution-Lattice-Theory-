# Hyper 213

**Status**: Closed (3 files).

## Overview

213-native handling of "hyper" arithmetic: tetration, Ackermann-style
recursion bounds, and very-large-number representation read against the
level-2 evaluation `configCountD 2 = 5²⁵`.

`5²⁵` is one value of the parametric family `configCountD : Nat → Nat`
(strictly increasing, no level privileged — `fractal.md` §7), **not** a
universe-constant cap on representable numbers.  Which hyper-values
close at level 2 is the level-relative question this chapter formalizes.

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
  evaluation level* (a level-choice, not a privileged cap; CLAUDE.md
  "Universe-constant framing" failure mode forbids treating any one
  value as the invariant), and dynamic readings (Pell-Fib, Möbius
  P^n, ...) do not close at the same level — only its bracket-class
  is representable there

Read level-relatively: a value exceeding `configCount 2` is not a cap
violation but a value read at the wrong evaluation level — the family
continues at `configCountD 3, 4, …` with no privileged ceiling.

## Connection

- `theory/math/numbertheory/dyadic_fsm.md` — FSM-based hyper recursion
