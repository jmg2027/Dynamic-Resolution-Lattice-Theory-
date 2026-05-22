# Math Tactic Infrastructure

**Status**: Closed (5 files: Ring213, HurwitzRing, QuadExtension, IntSquare, Test).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.  (algebra-213 meta-theorems algebra213_meta_theorems.md is the higher-level
narrative; this chapter is the tactic infrastructure layer.)

## Overview

213-native ring tactic infrastructure for closing polynomial
identities at the CD-tower levels: `Ring213` (base), `HurwitzRing`
(norm-multiplicativity), `QuadExtension` (quadratic), `IntSquare`
(Int² helpers).

## Lean source

- `lean/E213/Lib/Math/Tactic/` (5 files)
- ∅-axiom PURE (the tactics themselves; their use produces PURE
  theorems when applied)

## Narrative

See `theory/math/algebra213_meta_theorems.md` for the
meta-theoretical narrative.  This chapter documents the tactic
infrastructure separately:

- **`Ring213`** — base 213-native ring tactic.  Strategy: flatten
  polynomial → Int → decide via Nat bridges.  Replaces `ring` (which
  pulls propext).
- **`HurwitzRing`** — specialized for Hurwitz norm-multiplicativity
  identities (8-16 variable polynomials).
- **`QuadExtension`** — quadratic-extension identity closer.
- **`IntSquare`** — Int² supporting lemmas (used by all of the above).
- **`Test/`** — tactic test suite.

## Connection

- `theory/math/algebra213_meta_theorems.md` — meta-narrative
- `theory/math/cayley_dickson/algebra_tower.md` — primary tactic consumer
