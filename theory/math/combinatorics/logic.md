# Logic 213

**Status**: Closed (5 files; marathon-completed; blueprint retired).

## Overview

213-native logic: **atomic Bool LEM** (decidable on every Bool-valued
indicator) replaces classical LEM.  R1-R5 judgment-game framework.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Combinatorics/Logic/` (5 files)
- **Umbrella**: `Logic.lean`
- **Blueprint**: `blueprints/math/14_logic_213.md` (retired)
- **∅-axiom status**: PURE

## Narrative

Classical LEM (`P ∨ ¬P` for arbitrary `P`) is anti-constructive —
it imports `Classical.choice` in Lean.  213's version is the
**atomic Bool LEM**: for every Bool-valued indicator, `b = true ∨
b = false` decidably.

The R1-R5 judgment-game framework (per `seed/AXIOM/09_lean_correspondence.md` §9) provides the meta-discipline: each judgment has a typed protocol,
LEM applies only at the typed-Bool boundary.

## Connection

- `theory/math/foundations/cross_domain_unification.md` (C6) — Logic as paradigm
  instance
- `seed/AXIOM/09_lean_correspondence.md` — R1-R5 judgment game canonical
