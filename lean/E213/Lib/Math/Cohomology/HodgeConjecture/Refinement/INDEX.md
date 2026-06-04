# `HodgeConjecture/Refinement/` — refinement variants of Hodge conjecture

Refinement-side machinery: Lefschetz (hyperplane / (1,1)), standard
conjectures, Voisin's refinement, generalized Hodge.

## Files (6)

  - `LefschetzHyperplane.lean`    — Lefschetz hyperplane theorem
  - `LefschetzOneOne.lean`        — Lefschetz (1,1) theorem
  - `StandardConjectures.lean`    — Grothendieck standard conjectures
  - `Voisin.lean`                 — Voisin's refinement
  - `GeneralizedHodge.lean`       — generalized Hodge conjecture
  - `CupAtomicGeneration.lean`    — cup-atomic generation refinement

## Where to add new files

  - New Lefschetz variant       → `Lefschetz<...>`
  - New conjecture variant      → `<conjecturer>.lean` (e.g. Voisin)
  - Refinement variant          → `Generalized<...>` / `<...>Refinement`

## Companion sub-clusters (in `HodgeConjecture/`)

  - `Foundation/`     — base conjecture statement
  - `Pairing/`        — HIT + HR pairings
  - `MotivicBridge/`  — motive / étale bridge
  - `Toolkit/`        — auxiliary toolkit
