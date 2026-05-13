# `Lib/Math/Linalg213/` — 213-native linear algebra

213-native linear algebra (vectors / span / rank / Gram /
chirality / gap) without Mathlib.  Used by Hodge-pairing
arithmetic and physics couplings.

## Files (10 + Gap/ subdir)

### Core algebra
  - `Vector.lean`         — `Vector` base type
  - `Span.lean`           — linear-span operation
  - `Rank.lean`           — rank computation
  - `Rank5Concrete.lean`  — concrete rank-5 witness

### Gram + chirality + gap
  - `Gram.lean`             — Gram matrix
  - `Chiral.lean`           — chirality predicate
  - `PhaseChiralBridge.lean` — phase ↔ chirality bridge
  - `Gap.lean`              — spectral-gap top-level
  - `Gap/`                  — Gap sub-cluster (eigenvalue gap detail)

### Bridges + capstone
  - `Bridge.lean`           — bridge to physics couplings
  - `Capstone.lean`         — Linalg capstone

## Top-level

  - `Linalg213.lean` aggregator

## Where to add new files

  - New vector / span lemma   → `Vector*` / `Span*`
  - Rank / Gram lemma         → `Rank*` / `Gram*`
  - Chirality                 → `Chiral*` / `PhaseChiralBridge`
  - Gap / spectrum            → `Gap.lean` (top-level), `Gap/` (detail)
  - Bridge to external use    → `Bridge.lean`
