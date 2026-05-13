# `Lib/Physics/Atomic/` — atomic physics

Atomic-scale physics: hydrogen / helium baseline, screening,
bond angles, ionization energies (sub-cluster).

## Files (6 + IE/ sub-cluster)

### Per-element
  - `Hydrogen.lean`    — H baseline
  - `Helium.lean`      — He extension (electron-electron interaction)

### Structural
  - `Screening.lean`   — screening / shielding correction
  - `BondAngles.lean`  — bond-angle constraints
  - `Bridge.lean`      — bridge to other clusters

### Ionization sub-cluster
  - `IE/`              — ionization energies (15 files, see INDEX)

## Top-level

  - `Atomic.lean` aggregator
  - `IE.lean` IE sub-aggregator

## Where to add new files

  - New element baseline    → `<Element>.lean` (atomic structure)
  - New correction          → `<correction>.lean`
  - IE specific             → use `IE/` sub-cluster
  - Bond / molecular        → `Bond<...>` family

## Companion clusters

  - `Lib/Physics/Hadron/`     — hadronic physics
  - `Lib/Physics/Couplings/`  — gauge couplings
  - `Lib/Physics/Nuclear/`    — nuclear physics
  - `Lib/Physics/AlphaEM/`    — 1/α_em derivation
