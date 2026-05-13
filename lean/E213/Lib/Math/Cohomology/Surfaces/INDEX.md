# `Cohomology/Surfaces/` — Kähler surface cohomology specifics

Cohomology computations on specific Kähler surfaces: ℙ¹×ℙ¹, ℙ²,
T² (minimal), T²×T² (squared), T²ⁿ Betti numbers.

## Files (5 + sub-dirs)

### Surfaces (flat)
  - `P1Squared.lean`   — ℙ¹ × ℙ¹
  - `P2Minimal.lean`   — ℙ² minimal
  - `T2Minimal.lean`   — T² minimal (top-level)
  - `T2Squared.lean`   — T² × T² (top-level)
  - `T2nBetti.lean`    — T²ⁿ Betti numbers

### Sub-clusters
  - `T2Minimal/`       — T² detailed sub-cluster
  - `T2Squared/`       — T² × T² detailed sub-cluster

## Where to add new files

  - New surface           → `<Surface>.lean`  (or `<Surface>/` if
                             detailed enough to warrant sub-cluster)
  - Specific Betti / class → `<Surface><quantity>.lean`

## Companion clusters

  - `HodgeConjecture/Pairing/`   — HIT + HR (consumes surface results)
  - `Cohomology/Cup/`            — strict cup product
  - `Cohomology/CupAW/`          — Alexander-Whitney cup
