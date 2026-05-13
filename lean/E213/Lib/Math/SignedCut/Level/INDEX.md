# `SignedCut/Level/` — signed-cut level analysis (G38 / G39)

Level-25 / Level-26 specific signed-cut results.  G38 + G39
final capstones for the Cayley-Dickson tower at signed-cut level.

## Files (5)

  - `Level25Residual.lean`    — Level-25 residual analysis
  - `Level25Capstone.lean`    — Level-25 capstone
  - `Level26Absence.lean`     — Level-26 absence theorem
  - `G38FinalCapstone.lean`   — G38 final capstone
  - `G39Capstone.lean`        — G39 capstone

## Where to add new files

  - New level analysis     → `Level<N><kind>.lean`
  - Capstone               → `G<N>Capstone.lean` or
                              `Level<N>Capstone.lean`

## Companion sub-clusters (in `SignedCut/`)

  - `Core/`     — signed-cut algebra
  - `CD/`       — CD level operations (general)
  - `Hurwitz/`  — Hurwitz integers
  - `Octonion/` — octonion level
  - `Bridge/`   — external bridges
