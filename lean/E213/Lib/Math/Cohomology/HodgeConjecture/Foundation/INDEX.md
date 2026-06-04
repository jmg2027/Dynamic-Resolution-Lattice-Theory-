# `HodgeConjecture/Foundation/` — Hodge conjecture foundation primitives

Foundational scaffolding for the Hodge-conjecture programme: the
conjecture statement, canonical form, completeness witness,
Lens-catamorphism encoding.

## Files (6)

  - `Conjecture.lean`     — Hodge-conjecture statement (213-native)
  - `ConjectureLens.lean` — Lens-encoded conjecture form
  - `Canonical.lean`      — canonical-form normaliser
  - `Complete.lean`       — completeness witness
  - `Filled.lean`         — "filled" predicate (conjecture status)
  - `LensCata.lean`       — catamorphism over Lens witnesses

## Companion sub-clusters (in `HodgeConjecture/`)

  - `Structure/`     — combinatorial structure
  - `Pairing/`       — HIT + HR pairings (see INDEX)
  - `Refinement/`    — refinement-poset machinery
  - `Bridge/`        — bridges to physics / statmech (see INDEX)
  - `MotivicBridge/` — motive / étale bridge
  - `Toolkit/`       — auxiliary toolkit

## Where to add new files

  - Conjecture statement variant   → `Conjecture<...>` /
                                      `<...>Conjecture.lean`
  - Status / completeness          → `Complete.lean` / `Filled.lean`
  - Lens-encoded form              → `<...>Lens` / `LensCata`
