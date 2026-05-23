# Ordinary Differential Equations 213

**Status**: Closed (5 files).

## Overview

213-native ODE machinery: solutions as **explicit modulus-bracketed
sequences** on Real213 cuts.  The standard ODE existence-and-
uniqueness (Picard-Lindelöf) is stated with explicit precision
brackets at each step, not existential ε-δ.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/ODE/` (5 files)
- **∅-axiom status**: PURE

## Narrative

Classical ODE theory: given `y' = f(t, y)` with Lipschitz `f`,
**there exists** a unique solution.  In 213: the solution **is**
the Picard iteration sequence with explicit step modulus.

`y_{n+1}(t) = y_0 + ∫_0^t f(s, y_n(s)) ds`

at each iteration, the truncation error is bounded by an explicit
function of the Lipschitz constant + step count.  No existential.

## Connection to other chapters

- `theory/math/real213.md` — solutions are Real213-valued
- `theory/math/cauchy.md` — Picard iterates form Cauchy sequences
- `theory/math/modulus.md` — explicit moduli used here
