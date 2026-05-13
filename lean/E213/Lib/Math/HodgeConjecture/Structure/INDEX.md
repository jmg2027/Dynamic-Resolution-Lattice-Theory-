# `HodgeConjecture/Structure/` — cohomology-ring structure for Hodge

Algebraic-cohomology-ring structure on H*: ring, map, Poincaré
duality, Hard Lefschetz theorem.

## Files (5)

  - `Ring.lean`                — H* as a graded ring
  - `Map.lean`                 — ring map / pullback
  - `PoincareDuality.lean`     — Poincaré duality on T²ⁿ
  - `HardLefschetz.lean`       — Hard Lefschetz theorem (general)
  - `HardLefschetzT2Squared.lean` — Hard Lefschetz on T²×T²

## Where to add new files

  - Specific surface case   → `<Theorem><Surface>.lean`
  - Ring / map refinement   → `Ring*` / `Map*`

## Companion sub-clusters (in `HodgeConjecture/`)

  - `Foundation/`   — base conjecture
  - `Pairing/`      — HIT + HR pairings (consumes structure)
  - `Refinement/`   — Lefschetz refinements
