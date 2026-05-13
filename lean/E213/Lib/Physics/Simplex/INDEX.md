# `Lib/Physics/Simplex/` — Δ⁴ simplex + 3-generation structure

Δ⁴ simplex enumeration + 3-generation structure (relates to
fermion-family count = 3).

## Files (7)

### Counts + structure
  - `Counts.lean`              — Δ⁴ subset / face counts
  - `FaceTerms.lean`           — per-face term enumeration
  - `SubInventory.lean`        — sub-simplex inventory
  - `MultiComposite.lean`      — multi-composite assembly

### Spectrum + generation
  - `FoccSpectrum.lean`        — focc (focus on contact channel) spectrum
  - `Generations.lean`         — 3-generation count witness
  - `GenerationStructure.lean` — generation structural detail

## Top-level

  - `Simplex.lean` aggregator

## Where to add new files

  - New face / subset enumeration  → `Face<...>` / `Sub<...>`
  - Spectrum                        → `<focus>Spectrum.lean`
  - Generation theorem              → `Generation<...>`

## Connection

  - N_generations = 3 (DRLT prediction): closed by `Generations.lean`
  - `Substrate.Capstone` consumes simplex counts
