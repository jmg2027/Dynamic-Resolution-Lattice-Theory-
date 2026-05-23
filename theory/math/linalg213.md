# Linear Algebra 213

**Status**: Closed (15 files).

## Overview

213-native linear algebra: vectors, span, rank, Gram matrix,
phase-chiral bridge (G4 anchor).  Realized on Real213 cuts +
SignedCut for signed extensions.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Linalg213/` (15 files)
- **Umbrella**: `Linalg213.lean`
- **∅-axiom status**: PURE

## Narrative

Vectors are `Fin n → Real213`, span is finite-set generation,
rank is decidable (Gaussian elimination on rational pivots).

The **PhaseChiralBridge** (`PhaseChiralBridge.lean`) is the
formal anchor for G4 (d = 5 chiral / phase duality): the same
underlying 5-dim Linalg213 carrier admits two distinct readings
(chiral basis vs phase basis), related by a structural change-of-
basis.

Used downstream by:
- α_em Gram-self-energy (`AlphaEM/GramSelfConsistency.lean`)
- Hodge index theorems (Hodge chapter)

## Connection

- `research-notes/G4_chiral_phase_duality.md` (active foundational)
  — anchored here
- `theory/physics/alpha_em/precision_derivation.md` — Gram correction
