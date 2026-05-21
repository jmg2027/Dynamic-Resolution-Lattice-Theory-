# `Lib/Physics/Cosmology/` — cosmological observables

Cosmological-scale physics: Hubble constant, N_eff (effective
neutrino species), dark energy, gravity shadow, horizon information.

## Files (6)

  - `HubbleConstant.lean`     — H₀ derivation
  - `NeffDerivation.lean`     — N_eff (effective neutrino species)
  - `DarkEnergy.lean`         — dark-energy density / Λ
  - `GravityShadow.lean`      — gravity-shadow effect
  - `HorizonInformation.lean` — horizon-information bound
  - `Bridge.lean`             — bridge to other physics clusters

## Top-level

  - `Cosmology.lean` aggregator

## Where to add new files

  - New cosmological observable     → `<Observable>.lean`
  - Horizon / boundary effect       → `Horizon<...>` / `<...>Shadow`
  - Bridge to atomic base    → `Bridge.lean`
