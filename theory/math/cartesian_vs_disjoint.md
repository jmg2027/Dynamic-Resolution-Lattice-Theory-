# Cartesian vs Disjoint (G45)

**Status**: Closed (3 files, capstone `G45Capstone`).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 — G45 → chapter + archive.

## Overview

The classical conflation of **Cartesian product** (A × B) and
**disjoint union** (A ⊔ B) is broken in 213.  Each is a distinct
Lens application on the Raw substrate, with different cardinality
behaviors and different downstream properties.

The fix: **separate Lenses**, each with its own typed protocol,
not a single "product" that switches behavior by context.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/CartesianVsDisjoint/` (3 files)
- **Capstone**: `G45Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `CartesianCheck` | Cartesian-product check (cardinality A · B) |
| `DisjointVsProduct` | Disjoint-union vs product (cardinality A + B vs A · B) |
| `G45Capstone` | Cartesian-vs-disjoint master |

## Narrative

In ZFC, both A × B and A ⊔ B are sets — distinguishable but using
the same primitive (set-of-pairs).  In 213's lens framework, the
difference is more fundamental:

- **Cartesian (×)**: simultaneous Lens on two axes; output
  cardinality |A| · |B|; preserves bipartite structure
- **Disjoint (⊔)**: alternative Lens on two axes; output
  cardinality |A| + |B|; collapses bipartite structure into a
  single axis with tagged elements

The same elements can underlie both, but the Lens application
(and thus the downstream theorems available) differs.  Classical
"category-theoretic conflation" of these as "biproduct" or
"coproduct" obscures this distinction.

213 keeps them separate as named Lenses.  `CartesianCheck` and
`DisjointVsProduct` enforce the type-level separation; the capstone
proves that confusing them produces type errors.

## Research-note provenance

`research-notes/G45_cartesian_vs_disjoint.md` — archived.
