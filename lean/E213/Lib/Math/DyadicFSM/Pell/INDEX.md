# `DyadicFSM/Pell/` — Pell equation + dyadic FSM encoding

Pell equation `x² - D·y² = 1` and its dyadic-FSM encoding.  Lens
classification (single / pair / triple) + Proper-Pell norm-form
variant.

## Files (11)

### Core
  - `Family.lean`        — Pell solution family
  - `Bounds.lean`        — bound lemmas
  - `Capstone.lean`      — top-level Pell capstone

### Lens encodings
  - `Lens.lean`          — single-Lens encoding
  - `LensPairs.lean`     — Lens-pair classifier
  - `LensTriple.lean`    — Lens-triple classifier

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
  - Lens classifier      → `Lens` / `LensPairs` / `LensTriple`
  - Bound / family       → `Bounds` / `Family`

## Companion clusters

  - `DyadicFSM/ArithFSM/`     — Tier 1 multi-state FSM
  - `DyadicFSM/Pisano/`       — Pisano period analogue
  - `Lib/Math/Cauchy/PellSeq` — Pell sequence as Cauchy seq
