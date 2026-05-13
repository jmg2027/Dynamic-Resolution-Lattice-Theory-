# `HodgeConjecture/Bridge/` — Hodge ↔ physics / statmech / CS bridges

Bridge layer connecting Hodge-conjecture cohomology to external
models: algebraic geometry, statistical mechanics, discrete
geometry / phase, machine-learning decoders.

## Files (11)

### Algebraic geometry (3)
  - `BeilinsonRegulator.lean`   — Beilinson regulator construction
  - `MotiveEtaleFusion.lean`    — motive / étale fusion bridge
  - `GaloisCounterfactual.lean` — Galois-action counterfactual

### Statistical-mechanics models (4)
  - `Ising.lean`                — Ising-model Hodge-class encoding
  - `Potts.lean`                — Potts-model variant
  - `SpinGlass.lean`            — spin-glass setup
  - `SpinGlassGroundState.lean` — spin-glass ground-state classification

### Discrete geometry / phase (3)
  - `DiscreteGeometry.lean`     — discrete-geometry bridge
  - `PhaseRouting.lean`         — phase-routing model
  - `G6Vacuity.lean`            — G6 vacuity claim

### Computer science (1)
  - `MLDecoder.lean`            — ML-decoder bridge (algorithmic
                                  cup-class interpretation)

## Top-level

  - `Bridge.lean` aggregator (anti-corruption layer)

## Where to add new files

  - Algebraic-geometry bridge   → `<theorem-name>.lean` (Beilinson*,
                                  Motive*, Galois*)
  - Statmech model              → `<Model>.lean` (Ising-style)
  - Discrete / phase            → `Phase*` / `DiscreteGeometry*`
  - Algorithmic / CS            → `MLDecoder` family

## Bridge discipline

Per CLAUDE.md "Bridge.lean" pattern: this cluster is an
anti-corruption layer between Hodge cohomology and external
models.  External vocabulary stays inside the bridge; internal
results re-stated in 213-native terms.
