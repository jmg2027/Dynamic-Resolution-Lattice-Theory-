# Multivariable Calculus 213

**Status**: Closed (6 files).

## Overview

213-native multivariable calculus on Real213^n: partial derivatives,
gradients, Jacobians, the chain rule.  All operations carry
**explicit modulus** tracking per coordinate.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Multivariable/` (6 files)
- **∅-axiom status**: PURE

## Narrative

The standard multivariable calculus apparatus (partial derivatives,
gradients, Jacobians, Hessians) ports directly to Real213^n with
the substitution **ε-δ → modulus**.

Per the cross-domain unification (C6), multivariable calculus is one
of the 9 paradigm domain instances of the `CoeffSeq` graded ring —
multivariable polynomial = `Nat^n → Nat` lift of single-variable
`CoeffSeq`.

## Connection to other chapters

- `theory/math/real213.md` — Real213^n base
- `theory/math/cross_domain_unification.md` (C6) — paradigm domain
