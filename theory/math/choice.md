# Choice Infrastructure (213-native)

**Status**: Closed (4 files).

## Overview

Bootstrap witnesses for choice-like operations **without invoking
`Classical.choice`**.  When a downstream theorem would naively
need choice, the bootstrap witness provides the explicit
constructive alternative.

Includes `CanonicalTruthChar.lean` — the **only** pre-existing
`propext` usage in production code (sealed-by-design per
`STRICT_ZERO_AXIOM.md`).

## Lean source

- `lean/E213/Lib/Math/Foundations/Choice/` (4 files)
- ∅-axiom PURE except `CanonicalTruthChar` (sealed-by-design with propext)

| File | Purpose |
|---|---|
| `BootstrapWitness` | Constructive witness providing the "chosen" element |
| `Canonical` | Canonical-form selection |
| `CanonicalTruthChar` | Truth-characteristic (uses propext, sealed) |
| `Resolved` | Resolution helpers |

## Narrative

Classical mathematics uses `Classical.choice` to "pick" an element
from a non-empty set when no constructive rule exists.  213's
approach: **provide the construction**.  When a construction is
genuinely missing, the call must be sealed-by-design with explicit
justification.

`CanonicalTruthChar` is the one such sealed entry: it characterises
truth via propositional extensionality.  Avoiding this would
require a deeper refactor of the equality reasoning; the seal
documents the dependency.

## Connection

- `STRICT_ZERO_AXIOM.md` — `CanonicalTruthChar` listed as sealed-by-design
- `theory/lens/axiom_lenses.md` (layered-API classification Tier 4 A2) — propext as a Lens
