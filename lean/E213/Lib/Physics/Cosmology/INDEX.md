# `Lib/Physics/Cosmology/` — cosmological observables

Cosmological-scale physics: N_eff (effective neutrino species),
dark energy, horizon information, and the cosmological falsifiers
(e-folds, η_B).

## Files (6)

  - `NeffDerivation.lean`     — N_eff (effective neutrino species)
  - `DarkEnergy.lean`         — dark-energy density / Λ
  - `HorizonInformation.lean` — horizon-information bound
  - `EfoldsFalsifier.lean`    — inflation e-folds N = 60 atomic bracket
  - `EtaBFalsifier.lean`      — η_B leading 6 = NS·NT falsifier (F26)
  - `Bridge.lean`             — bridge to other physics clusters

## Top-level

  - `Cosmology.lean` aggregator

## Where to add new files

  - New cosmological observable     → `<Observable>.lean`
  - Horizon / boundary effect       → `Horizon<...>`
  - Bridge to atomic base    → `Bridge.lean`
