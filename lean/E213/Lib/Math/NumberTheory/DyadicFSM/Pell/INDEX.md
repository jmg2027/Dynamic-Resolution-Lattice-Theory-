# `DyadicFSM/Pell/` — Pell equation + dyadic FSM encoding

Pell equation `x² - D·y² = 1` and its dyadic-FSM encoding.  Lens
classification (single / pair / triple) + Proper-Pell norm-form
variant.

## Files (9)

### Core
  - `Family.lean`        — Pell solution family
  - `Bounds.lean`        — bound lemmas
  - `Capstone.lean`      — top-level Pell capstone

### Lens encodings
  - `LensCompositions.lean` — `Pell mod a × Pell mod b` CRT
                               closures at pair and triple
                               compositions (3×5, 3×7, 5×7,
                               3×5×7), plus BitFSM-form period
                               lifts for the base mods

### Proper-Pell (norm-form variant)
  - `Proper.lean`        — proper-Pell core
  - `ProperSmall.lean`   — small-D variant
  - `Proper8.lean`       — D = 8 case
  - `ProperBridge.lean`  — bridge to dyadic-FSM
  - `ProperMod.lean`     — per-mod variants consolidated (CLAUDE.md
                           rule 7: per-mod variants in one file)

## Top-level

  - `Pell.lean` aggregator

## Where to add new files

  - New per-mod variant  → consolidate into `ProperMod.lean`
                            (CLAUDE.md rule 7)
  - New D value          → `Proper<D>.lean` (small specific D)
  - Lens classifier      → `LensCompositions`
  - Bound / family       → `Bounds` / `Family`

## Companion clusters

  - `DyadicFSM/ArithFSM/`     — Tier 1 multi-state FSM
  - `DyadicFSM/Pisano/`       — Pisano period analogue
  - `Lib/Math/Analysis/Cauchy/PellSeq` — Pell sequence as Cauchy seq
