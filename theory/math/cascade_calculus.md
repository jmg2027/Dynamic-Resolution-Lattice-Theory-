# Cascade Calculus

**Status**: Closed (2 files).

## Overview

Cascade calculus: combinator + instance for **chained
rewrite-cascade reasoning** in 213.  Sibling of the rw-cascade
adoption (per scanner suite rw-cascade adoption gap finding).

## Lean source

- `lean/E213/Lib/Math/CascadeCalculus/` (2 files)
- ∅-axiom PURE

| File | Purpose |
|---|---|
| `Core` | Cascade combinator (chain of rewrites) |
| `Instance` | Instance scaffolding for cascade applications |

## Narrative

Many DRLT theorem proofs use `rw [a]; rw [b]; rw [c]; ...` cascades.
The cascade calculus provides a 213-native combinator that bundles
these into single typed steps with explicit type witnesses at each
cascade position.

Used by:
- Universe chain (Möbius P-matrix identities `P^10 ≡ I mod 5`)
- Algebra tower (recurrence rewrites)
- Cohomology cup-product chain rewrites

Sibling of rw-cascade adoption gap (scanner suite finding: `mul_left_comm`/`add_left_comm`
under-adoption); cascade_calculus is the **alternative direction** —
explicit combinator instead of cascade of named tactics.

## Connection

- `theory/meta/scanner_suite.md` — rw cascade adoption gap
