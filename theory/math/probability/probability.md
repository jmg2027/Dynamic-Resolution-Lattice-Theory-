# Probability 213 — Atomic Dyadic

**Status**: Closed (38 files).

## Overview

**Atomic dyadic probability** — no σ-algebra, no σ-additivity.
Probability in 213 is a **finite ratio of dyadic-FSM outcomes**;
every probability value lives in `Nat / 2^N` at resolution `N`.

Per the cross-domain unification (C6), probability is one of the
9 paradigm domain instances.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Probability/` (38 files)
- **Umbrella**: `Probability.lean`
- **∅-axiom status**: PURE

## Narrative

Classical probability uses σ-algebras + countable additivity.  213
has neither natively.  The atomic dyadic version:

- **Event** = `ProbabilityCut` (atomic dyadic mass; `Foundation/Cut.lean`)
- **Probability** = `(count of true) / 2^n`, finite rational
- **Independence** = product event = product probability (decidably)
- **Conditional** = ratio of finite counts

All standard probability theorems (law of large numbers,
Markov/Chebyshev) restate as **explicit-bracket** inequalities
on finite ratios.  No `∀ε > 0` — instead `∀ N, gap < 1/2^N` with
explicit modulus.

The 38 files cover: events, distributions, expectation, variance,
LLN (weak / strong with explicit modulus), Markov / Chebyshev,
joint / conditional, independence.

## Connection

- `theory/math/foundations/cross_domain_unification.md` (C6) — Probability as
  paradigm instance
- `theory/math/analysis/measure.md` — cup-product underlies probability
- `theory/math/probability/information.md` — bit-counting underlies probability
- `theory/math/numbertheory/dyadic_fsm.md` — dyadic FSM outcomes generate sample
  spaces
