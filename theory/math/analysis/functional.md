# Functional 213

**Status**: Closed (5 files).

## Overview

213-native functional analysis fragment: function spaces (Real213 →
Real213), bounded operators, the basic Banach-space-like
infrastructure needed for downstream physics (α_em precision, MVT
on couplings).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/Functional/` (5 files)
- **∅-axiom status**: PURE

## Narrative

Functional analysis in 213 is structurally the same as classical
(function spaces with norm) but with **explicit modulus** on every
norm-bound.  `‖f‖ ≤ M` means: there is an explicit function
producing M as a bound at any precision N.

Used downstream by `Lib/Physics/Couplings/` for MVT on running
couplings.

## Connection to other chapters

- `theory/math/numbersystems/real213.md` — function space base
- `theory/math/analysis/modulus.md` — explicit moduli
