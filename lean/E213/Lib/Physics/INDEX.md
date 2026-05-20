# `Lib/Physics/` — 213-native physics deployment (DRLT)

Physics deployment of the 213 axiom: atomic-base genesis, atomic /
hadron / nuclear / cosmological observables, gauge couplings,
α_em precision derivation, capstone synthesis.

DRLT = "Dynamic Resolution Lattice Theory" — the physics-deployment
name (vs the formal-axiom name 213).

## Top-level files (16 = 16 sub-cluster umbrellas)

### Atomic base + foundations (3)
  - `AtomicBase.lean`     — d=5, (NS, NT)=(3, 2), 10 pairs, c=2
  - `Foundations.lean`    — N_U scaffolding + atomic constants
  - `Capstones.lean`      — track-completeness + validation standard

### Gauge couplings + α_em (2)
  - `Couplings.lean`      — α_GUT, RunningGap, ThetaQCD, gauge spectrum
  - `AlphaEM.lean`        — 1/α_em = 137.0359991 derivation (C1 + C5)

### Mass / Higgs (2)
  - `Mass.lean`           — generic mass formulas
  - `Higgs.lean`          — Higgs mechanism

### Forces / gauge (2)
  - `YangMills.lean`      — YM mass gap + Weinberg angle
  - `Symmetry.lean`       — automorphism + chiral structure

### Atomic / hadron / nuclear (3)
  - `Atomic.lean`         — atomic-scale (incl. IE/ sub-cluster)
  - `Hadron.lean`         — hadron masses + ratios
  - `Nuclear.lean`        — nuclear binding + magic numbers

### Cosmology / mixing (2)
  - `Cosmology.lean`      — H₀, N_eff, dark energy
  - `Mixing.lean`         — CKM / PMNS / Cabibbo / CP violation

### Topological + Basel (2)
  - `Simplex.lean`        — Δ⁴ + 3-generation structure
  - `Basel.lean`          — Basel-form ζ(2) calculation

## Sub-directories (16)

Each top-level `.lean` is the aggregator for the matching directory;
see per-sub-cluster `INDEX.md` for file catalogs.

## DRLT Validation Standard (CLAUDE.md)

The physics track must satisfy at least one of:
  1. Strict ∅-axiom precision theorem (1/α_em, m_μ/m_e, m_p) at
     ppb–ppm precision.
  2. Strict ∅-axiom falsifier (N_gen = 3, θ_QCD < J·α⁴).

See `Capstones/ValidationStandardOne.lean` for criterion (1) status.

## Where to add new files

  - New observable cluster      → new directory + sub-aggregator
                                   `.lean` + `INDEX.md`
  - Single observable in cluster → matching cluster sub-directory
  - Capstone synthesis           → `Capstones/`
