# Math Extras

**Status**: Closed (8 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

Cross-cutting math utilities used by multiple sub-trees:
Cauchy-Schwarz inequality, inner-product Cauchy, Lp collapse,
Hoeffding finite-N bound, SymFin (symmetric finite groups),
real-log capstone, aggregator capstone.

## Lean source

- `lean/E213/Lib/Math/Extras/` (8 files)
- ∅-axiom PURE

## Narrative

These are mathematical primitives that don't fit cleanly into a
single domain sub-tree:
- **CauchySchwarz** — `(Σ a_i b_i)² ≤ (Σ a_i²)(Σ b_i²)` for Real213
  vectors; used in atomic_constants (AM-GM `2mn ≤ m² + n²` derives
  via this)
- **InnerCauchy** — Cauchy-Schwarz for inner-product spaces
- **LpOneCollapse** — Lp norm collapse to L1 at p=1
- **HoeffdingFiniteN** — Hoeffding inequality with explicit finite-N
  bound (used by Probability for LLN brackets)
- **SymFin** — symmetric groups on finite carriers
- **RealLogCapstone** — Real213 log identities
- **AggregatorCapstone** + **Capstone** — bundling capstones

## Connection

- `theory/physics/foundations/atomic_constants.md` — uses CauchySchwarz
- `theory/math/probability.md` — uses Hoeffding
- `theory/math/group.md` — SymFin instances
