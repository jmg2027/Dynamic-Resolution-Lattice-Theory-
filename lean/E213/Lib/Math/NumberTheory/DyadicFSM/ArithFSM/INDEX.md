# `DyadicFSM/ArithFSM/` — multi-state arithmetic FSM (Tier 1)

Captures Pell-like sequences for algebraic irrationals as
multi-state arithmetic recurrences `ArithFSM2 n` with state vector
`Fin n × Fin n` updating via a linear recurrence mod `n`.

## Files (14)

### Versioned development line
  - `V1.lean`         — V1: initial form
  - `V1to2.lean`      — V1 → V2 bridge
  - `V3.lean`         — V3: stable form
  - `V3Bound.lean`    — V3 bounds
  - `V3Equiv.lean`    — V3 equivalences
  - `V3Hardness.lean` — V3 hardness witness
  - `V3toBitFSM.lean` — V3 → BitFSM conversion

### Modulus buckets (S/M/L consolidation, 2026-05-12)
  - `ModSmall.lean`  — small N (2 ≤ N ≤ 8?)
  - `ModMedium.lean` — medium N
  - `ModLarge.lean`  — large N

### Structural
  - `Signature.lean`  — ArithFSM2 signature shape
  - `Hierarchy.lean`  — hierarchy across versions
  - `Hardness.lean`   — generic-hardness lemma
  - `ToBitFSM.lean`   — ArithFSM2 → BitFSM conversion

## Top-level

  - `ArithFSM.lean` aggregator + base `ArithFSM2 n` type definition

## Where to add new files

  - New per-modulus class    → consolidate into `ModSmall` /
                                `ModMedium` / `ModLarge` (don't
                                create new files per modulus —
                                CLAUDE.md rule 7)
  - New version              → `V<n>*` style
  - Conversion to BitFSM     → `ToBitFSM` / `V<n>toBitFSM`
  - Structural / hardness    → `Signature` / `Hardness` / `Hierarchy`
