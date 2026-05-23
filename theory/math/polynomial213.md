# Polynomial 213

**Status**: Closed (3 files).

## Overview

213-native polynomial machinery: polynomials as `CoeffSeq` (= `Nat → Nat`)
with finite support, evaluation, multiplication via convolution
(Cauchy product).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Polynomial213/` (3 files)
- **∅-axiom status**: PURE

## Narrative

Per the cross-domain unification (C6), polynomials and generating
functions share the same `CoeffSeq` underlying type.  `Polynomial213`
specializes `CoeffSeq` to **finite support** (polynomial ≠
generating function in this specialization).

Used by:
- `Lib/Math/Tactic/Ring213` for polynomial identity checking
- `theory/math/algebra213_meta_theorems.md` for CD ring identities

## Connection

- `theory/math/combinatorics.md` — `CoeffSeq` shared
- `theory/math/algebra213_meta_theorems.md` — polynomial-identity tactics
