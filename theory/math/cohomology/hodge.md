# Cohomology — Hodge

**Status**: Closed.

## Overview

Δ-Laplacian + ⋆-involution machinery. 9 + 1 files including
`InvolutionTemplate` — a unified template that the Prop/Prop52/53/54
involutions instantiate.  Hodge involution `⋆⋆ = id` on 5 Δ⁴ strata
(the 213-native (p,p)-decomposition).

## Lean source

- `lean/E213/Lib/Math/Cohomology/Hodge/`
- ∅-axiom PURE on production critical path

Key files:
- `Prop.lean`, `Prop52.lean`, `Prop53.lean`, `Prop54.lean` — per-stratum involution closures (decide-checked)
- `InvolutionTemplate.lean` — unified template the Prop* files instantiate.  Refactor consolidating the per-stratum proof structure into one parametric witness.

## Connection

- `theory/math/cohomology/hodge.md` — cup-chain cohomology + ⋆⋆ involution
- Other cohomology sub-clusters cite this layer
