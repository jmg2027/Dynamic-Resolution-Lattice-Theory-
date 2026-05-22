# Modular Arithmetic 213

**Status**: Closed (9 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

213-native modular arithmetic: Bézout's identity, GCD via Euclidean
algorithm, modular inverse, Chinese Remainder Theorem.  All
**explicit-witness** (no existential) — Bézout coefficients are
computed, GCD has explicit step bound.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/ModArith/` (9 files)
- **Umbrella**: `ModArith.lean`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `GCD` | Euclidean algorithm GCD |
| `Bezout` | Bézout coefficients (s, t) with `s·a + t·b = gcd a b` |
| `ModInv` | Modular inverse via Bézout |
| `CRT` | Chinese Remainder Theorem |
| ... | (5 more) |

## Narrative

Standard `Nat.gcd` uses Lean's well-founded recursion.  213's
`GCD` is dyadic-FSM-style: explicit step-count bound (≤ log_2 of
smaller input).  Bézout coefficients are returned as part of
the GCD output (not Skolemized).

CRT is used in the universe chain (Step 12: lcm(5, 2) = 30).

## Connection

- `theory/math/universe_chain.md` — CRT decomposition (mod 5, mod 2)
- `theory/math/dyadic_fsm.md` — dyadic FSM realization of GCD
- `theory/physics/foundations/atomic_constants.md` — C2 uses
  `Nat.lt` + `Nat.sub` bridges similar to ModArith
