# `Lib/Physics/Hadron/` — hadronic mass + ratio derivations

Hadronic-scale physics: quark mass hierarchy, proton mass, neutron-
proton ratio, proton g-factor, proton-electron mass ratio.

## Files (9)

  - `Masses.lean`              — generic hadron mass formulas
  - `QuarkHierarchy.lean`      — quark mass hierarchy
  - `ProtonMass.lean`          — proton mass derivation
  - `ProtonG.lean`             — proton g-factor
  - `NeutronProton.lean`       — neutron-proton mass ratio
  - `ProtonElectronRatio.lean` — m_p / m_e ratio
  - `Bigrading.lean`           — bigrading structure
  - `Bridge.lean`              — bridge to other physics clusters

## Top-level

  - `Hadron.lean` aggregator
  - `MtOverMc.lean` — m_t/m_c quark-mass chain atomic skeleton sum (NS·d² + NS·NT² = 87)

## Where to add new files

  - New hadron mass         → `<Hadron>Mass.lean`
  - Mass ratio              → `<H1><H2>Ratio.lean`
  - Form factor             → `<Hadron>G.lean` / `<Hadron><factor>.lean`
  - Structure / bridge      → `Bigrading.lean` / `Bridge.lean`

## Companion clusters

  - `Lib/Physics/Couplings/`  — gauge couplings (α_QCD)
  - `Lib/Physics/Atomic/`     — atomic physics (ionization energies)
  - `Lib/Physics/Nuclear/`    — nuclear physics
