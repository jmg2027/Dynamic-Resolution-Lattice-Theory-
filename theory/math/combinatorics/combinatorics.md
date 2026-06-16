# Combinatorics 213

**Status**: Closed (7 files).

## Overview

213-native combinatorics: binomial coefficients, generating
functions, finite-set enumeration.  All counts are decidable on
finite-Lens outputs.  Per the cross-domain unification (C6),
combinatorics is one of the 9 paradigm domain instances of the
`CoeffSeq` graded ring.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Combinatorics/` (7 files)
- **Umbrella**: `Combinatorics.lean`
- **Blueprint**: `blueprints/math/10_combinatorics_213.md` (retired)
- **∅-axiom status**: PURE

| File | Topic |
|---|---|
| `Binomial` | `binom n k` + Pascal recurrence |
| `GeneratingFunction` | `CoeffSeq := Nat → Nat` + convolution |
| `Capstone` | Master |
| ... | (4 more sub-files) |

## Narrative

Combinatorial primitives in 213 are **structurally decidable** —
every counting predicate reduces to a finite enumeration at any
chosen `configCount` family-evaluation level (typically n = 2 for
physics-side work).  The `GeneratingFunction.CoeffSeq` provides the
graded-ring underlying type used in:

- Cross-domain unification (C6) — paradigm domain instances
- AlphaEM C5 — Laplacian spectrum as `CoeffSeq`
- Hodge cohomology — cup-product = convolution

## Connection

- `theory/math/combinatorics/graph_connectivity.md` — abstract
  graph-connectedness induction (`Reach` → δ⁰-closed colouring is
  constant); underwrites the universal bipartite δ⁰-kernel result
- `theory/math/foundations/cross_domain_unification.md` (C6) — Combinatorics
  as paradigm instance
- `theory/physics/alpha_em/precision_derivation.md` — `CoeffSeq`
  spectrum bracket
- `theory/math/cohomology/hodge.md` — cup as convolution
