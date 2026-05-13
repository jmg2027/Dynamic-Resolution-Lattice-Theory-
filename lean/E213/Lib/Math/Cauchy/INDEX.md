# `Lib/Math/Cauchy/` — Cauchy / Euler / Wallis / Pell sequences

213-native sequence machinery: monotone-bounded, Archimedean
property, profinite sequences, and classical sequence families
(Euler, Wallis, Pell, generic).

## Files (7)

### Generic + properties
  - `GenericFamily.lean`     — generic Cauchy-family combinator
  - `MonotonicBounded.lean`  — monotone-bounded ⇒ Cauchy
  - `Archimedean.lean`       — Archimedean property
  - `ProfiniteSeq.lean`      — profinite sequence type

### Specific sequences (consolidated 2026-05-12)
  - `Euler.lean`             — Euler-formula sequence + Cauchy
                                (consolidated from 6 → 1)
  - `Wallis.lean`            — Wallis product (consolidated 3 → 1)
  - `PellSeq.lean`           — Pell sequence as Cauchy seq

## Companion clusters

  - `Real213/Cauchy/ChainToCut`   — Cauchy chain → cut bridge
  - `Real213/ExpLog/*Cauchy*`     — exp/log series convergence
  - `DyadicFSM/Pell/`             — Pell FSM encoding
  - `Math/Analysis/<...>Cauchy*`  — analysis-level Cauchy

## Where to add new files

  - New sequence family   → `<Sequence>.lean` (consolidate
                            evolution-of-the-same-topic per
                            CLAUDE.md rule 7)
  - New property          → `Monotone*` / `Archimedean*` /
                            `Profinite*`
