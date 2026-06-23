# Measure 213

**Status**: Closed (6 files).

## Overview

213-native measure theory: a measurable set is a **list of dyadic
brackets**, and measure is the **Nat sum of bracket lengths**.  No
σ-algebra, no countable additivity — finite bracket-counting carries the
whole construction.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/Measure/` (6 files)
- **∅-axiom status**: PURE

## Narrative

Classical measure theory uses σ-algebras + countable additivity to
define measure.  213 doesn't have native σ-additivity (per the
resolution limit + no completed infinities), so measure is
re-realized by **dyadic-bracket counting**:

- "Measurable set" = `DyadicMeasurableSet := List DyadicBracket`
  (`MeasurableSet.lean`), with `emptySet`, `singleton`, and `union`
  (list append).
- "Measure" = `measureNum : List DyadicBracket → Nat`
  (`DyadicMeasure.lean`), summing each bracket's length
  `bracketMeasureNum db := db.lenNum`.  Additivity is the theorem
  `measureNum_append : measureNum (s ++ t) = measureNum s + measureNum t`.
- "Lebesgue integral" = `lebesgueStepNum : (Nat → Nat) → List DyadicBracket → Nat`
  (`LebesgueIntegral.lean`), a step-integrand weighted bracket sum.

`OuterMeasure.lean` and `Lp.lean` build the outer-measure and Lᵖ-norm
(`lpNormPow`) layers on the same bracket-sum primitive; `Capstone.lean`
collects the witnesses.

## Connection to other chapters

- `theory/math/probability/probability.md` — atomic dyadic probability is the
  σ-free measure-theoretic counterpart
