# `Lib/Physics/Couplings/` — gauge couplings + running

Coupling-constant derivations: α_GUT, α_QCD running, gauge-coupling
spectrum, photon kernel, color confinement, Dyson structure,
asymptotic freedom, θ_QCD.

## Files (11)

### Unification + spectrum
  - `AlphaGUT.lean`         — α_GUT = 6/(25·π²) numerator/denominator
  - `GUTUnification.lean`   — gauge-coupling unification witness
  - `TripleCoupling.lean`   — SU(3)×SU(2)×U(1) coupling triple
  - `SpectrumComplete.lean` — full coupling-constant spectrum

### Running
  - `RunningGap.lean`         — IR-UV running gap
  - `AsymptoticFreedom.lean`  — QCD asymptotic-freedom witness

### Strong interaction
  - `ColorConfinement.lean`   — color-confinement scaffolding
  - `ClosedPropagator.lean`   — closed-form propagator
  - `DysonStructure.lean`     — Dyson tail structure
  - `ThetaQCD.lean`           — θ_QCD < J·α⁴ falsifier

### Electromagnetism
  - `PhotonKernel.lean`       — photon-propagator kernel

## Top-level

  - `Couplings.lean` aggregator

## Where to add new files

  - New unification / spectrum    → `<...>Unification` /
                                     `Spectrum<...>`
  - Running / gap                 → `Running<...>`
  - Strong-interaction structure  → `Color*` / `Dyson*` / `Theta*`
  - Electromagnetism              → `Photon<...>`

## Connection to other clusters

  - `Lib/Physics/AlphaEM/` — 1/α_em IR derivation (consumes
    `AlphaGUT` + `RunningGap`)
  - `Lib/Physics/Substrate/` — substrate that hosts couplings
