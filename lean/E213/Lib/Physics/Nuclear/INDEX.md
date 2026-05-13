# `Lib/Physics/Nuclear/` — nuclear-scale physics

Nuclear binding energy, magic numbers, deuteron binding, shell
structure.

## Files (6)

  - `Binding.lean`             — generic nuclear binding-energy
  - `DeuteronBinding.lean`     — deuteron binding (specific A=2)
  - `Shells.lean`              — nuclear shell structure
  - `MagicNumbers.lean`        — magic numbers (2, 8, 20, 28, 50, 82, …)
  - `MagicNumbersAtomic.lean`  — magic-number-atomic correspondence
  - `Bridge.lean`              — bridge to other physics clusters

## Top-level

  - `Nuclear.lean` aggregator

## Where to add new files

  - Specific isotope binding     → `<Isotope>Binding.lean`
  - Shell-level theorem          → `Shells*` family
  - Magic-number variant         → `MagicNumbers<...>`
  - Bridge to atomic / hadron    → `Bridge.lean`
