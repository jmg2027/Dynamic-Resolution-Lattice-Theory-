# `Lib/Physics/Capstones/` — physics-track capstone results

Top-level capstones synthesizing the entire physics derivation:
finitist observable chain, master catalog, pure-atomic observables,
DRLT Validation Standard.

## Files (5)

  - `MasterCatalog.lean`             — master observable catalog
  - `PhysicsTrackComplete.lean`      — physics-track completeness
  - `FinitistObservableChain.lean`   — finitist observable chain
  - `PureAtomicObservables.lean`     — pure-atomic observable set
  - `ValidationStandardOne.lean`     — CLAUDE.md validation standard
                                       criterion (1)

## Top-level

  - `Capstones.lean` aggregator

## Where to add new files

  - New capstone synthesis    → `<Topic>Capstone.lean` /
                                 `<Topic>Complete.lean`
  - Validation criterion      → `ValidationStandard<N>.lean`
  - Catalog refinement        → `<Topic>Catalog.lean`
