# Multivariable Calculus 213

**Status**: Closed (6 files).

## Overview

213-native multivariable calculus on Real213^n: partial derivatives,
gradients, Jacobians, the chain rule.  Operations act on `MultiCut n`
cut functions, with convergence handled by the modulus discipline of
the underlying Real213 cuts.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/Multivariable/` (6 files)
- **∅-axiom status**: PURE

## Narrative

Multivariable calculus is the `Nat^n → Nat` reading of the one
`CoeffSeq` graded ring; partial derivatives, gradients, Jacobians,
and Hessians are its count-Lens readouts (the apparatus that
classically carries an **ε-δ** is here the **modulus** on each
coordinate's underlying Real213 cut).

Per the cross-domain unification (C6), multivariable calculus is one
of the 9 paradigm domain instances of the `CoeffSeq` graded ring —
multivariable polynomial = `Nat^n → Nat` lift of single-variable
`CoeffSeq`.

## Connection to other chapters

- `theory/math/numbersystems/real213.md` — Real213^n base
- `theory/math/foundations/cross_domain_unification.md` (C6) — paradigm domain
