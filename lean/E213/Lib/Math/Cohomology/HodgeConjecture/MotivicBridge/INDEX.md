# `HodgeConjecture/MotivicBridge/` — motivic / étale-cohomology bridges

Bridges between 213-cohomology and motivic / Tate / Hodge-Tate
structures.  Beilinson-Lichtenbaum, Bloch-Beilinson, Mumford-Tate,
Chern character.

## Files (6)

  - `BeilinsonLichtenbaum.lean` — Beilinson-Lichtenbaum conjecture
  - `BlochBeilinson.lean`        — Bloch-Beilinson conjecture
  - `Tate.lean`                  — Tate conjecture
  - `HodgeTate.lean`             — Hodge-Tate variant
  - `MumfordTate.lean`           — Mumford-Tate group
  - `ChernCharacter.lean`        — Chern character bridge

## Where to add new files

  - Additional motivic conjecture     → `<name>.lean`
  - Specific cohomology theory bridge → `<theory>Bridge.lean`

## Companion sub-clusters (in `HodgeConjecture/`)

  - `Foundation/`   — base conjecture
  - `Bridge/`       — physics / statmech bridges (different audience)
  - `Refinement/`   — Lefschetz / Voisin refinements
