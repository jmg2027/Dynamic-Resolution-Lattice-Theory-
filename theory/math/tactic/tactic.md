# Math Tactic Infrastructure

**Status**: Closed (5 top-level files: Ring213, HurwitzRing, QuadExtension, IntSquare, Extras; plus `Extras/` and `Test/` sub-trees).

## Overview

213-native infrastructure for closing polynomial
identities at the CD-tower levels: `Ring213` (recurrence-as-definition
infra), `HurwitzRing` (norm-multiplicativity), `QuadExtension`
(quadratic), `IntSquare` (Int² helpers).

## Lean source

- `lean/E213/Lib/Math/Tactic/` (5 top-level files + `Extras/`, `Test/`)
- ∅-axiom PURE (the tactics themselves; their use produces PURE
  theorems when applied)

## Narrative

See `theory/math/foundations/algebra213_meta_theorems.md` for the
meta-theoretical narrative.  This chapter documents the tactic
infrastructure separately:

- **`Ring213`** — recurrence-as-definition infrastructure (no macro
  or syntax): define a sequence via the desired recurrence so it
  holds by `rfl`, with pointwise `decide` verification.  Used for
  linear recurrences on Nat-indexed Int sequences.
- **`HurwitzRing`** — the `hurwitz_ring` tactic: flatten a CD-tower
  identity componentwise → Int polynomial → `decide`/omega.
  Specialized for Hurwitz norm-multiplicativity identities (8-16
  variable polynomials).
- **`QuadExtension`** — quadratic-extension identity closer.
- **`IntSquare`** — Int² supporting lemmas (used by all of the above).
- **`Extras`** — additional supporting lemmas (umbrella over `Extras/`).
- **`Test/`** — tactic test suite.

## Connection

- `theory/math/foundations/algebra213_meta_theorems.md` — meta-narrative
- `theory/math/algebra/cayley_dickson/algebra_tower.md` — primary tactic consumer
