# `HodgeConjecture/Bridge/` — cohomology ↔ statmech / CS bridges

Bridge layer connecting cup-chain cohomology on K_5 / K_{3,2}^{(c=2)}
to statistical-mechanics + discrete-geometry + ML-decoder models.

## Files (7)

### Statistical-mechanics models (4)
  - `Ising.lean`                — K_5 Ising energy spectrum + routing
  - `Potts.lean`                — q=3 Potts variant
  - `SpinGlass.lean`            — spin-glass setup
  - `SpinGlassGroundState.lean` — spin-glass ground-state classification

### Discrete geometry (2)
  - `DiscreteGeometry.lean`     — discrete-geometry bridge
  - `ClassAExactWitnesses.lean` — exact-witness vacuity classification

### Computer science (1)
  - `MLDecoder.lean`            — ML-decoder bridge (algorithmic
                                  cup-class interpretation)

## Top-level

  - `Bridge.lean` aggregator (anti-corruption layer)

## Bridge discipline

Per CLAUDE.md "Bridge.lean" pattern: external vocabulary stays inside
the bridge; internal results re-stated in 213-native terms.
