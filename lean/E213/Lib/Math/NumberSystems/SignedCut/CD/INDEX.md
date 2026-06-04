# `SignedCut/CD/` — signed-cut Cayley-Dickson operations

SignedCut applied across the Cayley-Dickson tower: norm, conjugation,
level-by-level operations, mul rule, capstone.

## Files (6)

  - `CDConjugation.lean`     — Cayley-Dickson conjugation on signed cut
  - `CDNorm.lean`            — signed-cut norm
  - `CDMulRule.lean`         — multiplication rule
  - `CDLevelOps.lean`        — level-by-level operations
  - `CDTowerLevel.lean`      — tower-level structure
  - `CDTowerCapstone.lean`   — tower capstone result

## Companion sub-clusters (in `SignedCut/`)

  - `Core/`     — base signed-cut algebra
  - `Hurwitz/`  — Hurwitz integer signed
  - `Level/`    — level tower analogues
  - `Octonion/` — octonion level
  - `Bridge/`   — bridges to other clusters

## Where to add new files

  - New level operation        → `CDLevel<...>` / `CD<Level><op>.lean`
  - Conjugation / norm variant → `CDConjugation*` / `CDNorm*`
  - Tower capstone             → `CDTower<...>Capstone`
