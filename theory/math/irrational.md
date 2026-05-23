# Irrational 213

**Status**: Closed (3 files).

## Overview

213-native handling of irrational numbers: √2, φ (golden ratio),
e, π — as Real213 cuts with explicit bracket sequences from Pell,
Fib, Euler, Wallis families.

No "irrational" is a foundational object; each is a structural
output of the Cauchy sequence machinery.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Irrational/` (3 files)
- **∅-axiom status**: PURE

## Narrative

Classical mathematics distinguishes rationals from irrationals as
an ontological category.  213 doesn't — every Real213 value is a
finite-bracket sequence; the "irrationals" are just values whose
brackets never collapse to a single rational at finite depth.

`Irrational` provides:
- `√2` via Pell sequence brackets
- `φ` via Fibonacci ratio brackets
- `e` via Euler series brackets
- `π` via Wallis product brackets

Each is a **structural output**, not a foundational primitive.

## Connection

- `theory/math/cauchy.md` — Cauchy/Euler/Wallis/Pell families
- `theory/math/real213.md` — Real213 cuts as carrier
- `theory/math/universe_chain.md` — φ as universe-chain fixed point
