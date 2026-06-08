# `Lib/Math/Algebra/Linalg213/` — 213-native linear algebra

213-native linear algebra (vectors / span / rank / Gram /
chirality / gap) without Mathlib.  Used by Hodge-pairing
arithmetic and physics couplings.

## Files (core algebra + Gram/gap + the determinant stack + Gap/ subdir)

### Core algebra
  - `Vector.lean`         — `Vector` base type
  - `Span.lean`           — linear-span operation
  - `Rank.lean`           — rank computation
  - `Rank5Concrete.lean`  — concrete rank-5 witness

### Gram + chirality + gap
  - `Gram.lean`             — Gram matrix
  - `Chiral.lean`           — chirality predicate
  - `PhaseChiralBridge.lean` — phase ↔ chirality bridge
  - `Gap.lean`              — spectral-gap top-level
  - `Gap/`                  — Gap sub-cluster (eigenvalue gap detail)

### Determinant + permutations (the Leibniz / cofactor / Cayley–Hamilton stack)
  - `DetN.lean`           — recursive `n×n` determinant (`det`, cofactor/Laplace)
  - `Permutation.lean`    — `LPerm`, inversion-sign `psign`, the Leibniz `leibDet`
  - `PermGroup.lean`      — the symmetric group on value-lists (`composeList`, identity, assoc, `invPerm`)
  - `PermSign.lean`       — ★ sign-multiplicativity `psign(σ∘τ) = psign σ·psign τ` (bubble-sort)
  - `PermMatrixDet.lean`  — ★ `det(permMatrix σ) = psign σ`: the two readings of a permutation agree (Leibniz sum collapses to the surviving `τ=σ` term)
  - `PermClosure.lean`    — enumeration sound/complete/nodup; alternating + multilinear
  - `Laplace.lean`        — cofactor expansion, `leibDet_eq_det`, adjugate `M·adj M = det·I`
  - `DetTranspose.lean`   — ★★★ `det Mᵀ = det M` (psign_inv + invPerm involution + product-reindex)
  - `DetMul.lean`         — ★★★ `det(M·N) = det M·det N`: perm-group closure + row-permutation det + Cauchy–Binet expansion + constructive pigeonhole
  - `PermBridge.lean`     — the two `perms` enumerations coincide; `leibDet` is a sum of `n!` terms
  - `CayleyHamilton.lean` — matrix ring + integer Cayley–Hamilton `χ_M(M)=0`
  - `CharPolyAdj.lean` / `PolyDet.lean` — polynomial adjugate identity over `ℤ[X]`
  - `DetTriangular.lean` / `DetScale.lean` / `DetZeroCol.lean` — determinant corollaries
  - `DetRowOps.lean`      — elementary row operations (`rowᵢ += t·rowⱼ` preserves `det`)
  - `ProdLperm.lean` / `ProdCongr.lean` / `SumLinear.lean` / `RowDependence.lean` — det infra
  - `FibCassiniDet.lean` — Cassini/Fibonacci determinant witness

### Bridges + capstone
  - `Bridge.lean`           — bridge to physics couplings
  - `Capstone.lean`         — Linalg capstone

## Top-level

  - `Linalg213.lean` aggregator

## Where to add new files

  - New vector / span lemma   → `Vector*` / `Span*`
  - Rank / Gram lemma         → `Rank*` / `Gram*`
  - Chirality                 → `Chiral*` / `PhaseChiralBridge`
  - Gap / spectrum            → `Gap.lean` (top-level), `Gap/` (detail)
  - Determinant / permutation → `DetN` / `Permutation` / `PermClosure` /
                                `Laplace` / `PermBridge`
  - Bridge to external use    → `Bridge.lean`
