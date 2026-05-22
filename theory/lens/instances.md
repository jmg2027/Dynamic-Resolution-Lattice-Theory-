# Lens Instances Catalog

**Status**: Closed (35 files — largest Lens sub-tree).
**Promoted from research-notes**: 2026-05-22.

## Overview

**Concrete `Lens α` instances** for specific α codomains.  Each
file provides one or more concrete Lens — useful as building blocks
for downstream constructions.

## Lean source

- `lean/E213/Lens/Instances/` (35 files)
- ∅-axiom PURE

## Narrative

Important instances:
- **NatLens** — Raw → ℕ (count of distinguishings)
- **BoolLens** — Raw → Bool (per Bool213)
- **PairLens** — Raw → α × β (compose two Lenses)
- **OptionLens** — Raw → Option α (with default for null Raw)
- **ListLens** — Raw → List α (sequence of Lens applications)
- **PrismLens** — Raw → Sum α β (case-split Lens)
- **SetLens** — Raw → Set α (multi-output Lens)
- **TreeLens** — Raw → Tree α (recursive structure-preserving)
- **NumberSystemLens** — Raw → (specific number system per Nat213)
- ... ~25 more

Each is decidable + small + composable.  Together they constitute
the **library of Lens primitives** that other DRLT layers (Math,
Physics) build on.

`PrismLens` ↔ truth-table identities (G98 unfold-graph candidate
N7, see scanner_suite.md).

## Connection

- All `theory/lens/*` chapters compose these
- `theory/math/*` chapters use specific instances
- `lean/E213/docs/PROMOTION_PATTERNS.md` references PrismLens example
