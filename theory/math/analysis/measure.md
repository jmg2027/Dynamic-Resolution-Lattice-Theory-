# Measure 213

**Status**: Closed (5 files).

## Overview

213-native measure theory: **cup-product algebra** replaces σ-additive
measure.  Per the cross-domain unification (C6), measure theory is
one of the 9 paradigm domain instances; the cup-product is the
graded-ring instantiation.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/Measure/` (5 files)
- **∅-axiom status**: PURE

## Narrative

Classical measure theory uses σ-algebras + countable additivity to
define measure.  213 doesn't have native σ-additivity (per the
resolution limit + no completed infinities), so measure is
re-realized via **cup-product**:

- "Measurable set" = `Cochain n k` indicator (Bool-valued on basis)
- "Measure" = cup-product evaluation on cochains
- "Lebesgue integral" = cup-pairing with Real213-valued integrand

This is the cup-as-measure paradigm shift (per chiral cup ring catalog §C6).

## Connection to other chapters

- `theory/math/foundations/cross_domain_unification.md` (C6) — measure as
  paradigm instance
- `theory/math/cohomology/hodge_conjecture.md` — cup-pairings on T²
  use the same machinery
- `theory/math/probability/probability.md` — atomic dyadic probability is the
  σ-free measure-theoretic counterpart
