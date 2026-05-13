# `Cohomology/Delta/` — boundary / coboundary operator δ

The δ (boundary / coboundary) operator on the 213 cochain complex:
linearity, pointwise behavior, δ² = 0, V4 capstone.

## Files (5)

  - `Core.lean`        — base `delta` operator
  - `Linear.lean`      — `δ(α + β) = δα + δβ` linearity
  - `Pointwise.lean`   — pointwise computation
  - `SqZero.lean`      — `δ² = 0` (cohomology base law)
  - `V4Capstone.lean`  — V4 capstone result

## Where to add new files

  - δ-rule extension   → `<rule>.lean` (Linear, Pointwise pattern)
  - Specific dim case  → `V<n>Capstone.lean`

## Companion clusters

  - `Cohomology/Cochain/`  — cochain base type
  - `Cohomology/Cup/`      — strict cup product (consumes δ²=0)
  - `Cohomology/CupAW/`    — AW cup product (consumes δ²=0)
