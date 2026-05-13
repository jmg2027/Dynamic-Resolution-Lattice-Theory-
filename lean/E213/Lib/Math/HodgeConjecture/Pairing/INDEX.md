# `Lib/Math/HodgeConjecture/Pairing/` — H* pairings (Hodge Index + Hodge-Riemann)

Cup-product pairings on H* and their signatures.  Hodge Index
Theorem (HIT) and Hodge-Riemann positivity (HR) — first vacuously
on K_{3,2}^{(c=2)}, then non-vacuously on Kähler 2-folds (T², ℙ²,
ℙ¹×ℙ¹, T²×T²) and parametric generalisations.

## Files (21)

### Base capstones (vacuous on K, non-vacuous lifts) (4)
  - `HodgeIndex.lean`       — base on K_{3,2}^{(c=2)} (cup vacuously 0)
  - `HodgeRiemann.lean`     — base HR (positivity vacuous in ℤ/2)
  - `HodgeIndexT2.lean`     — ★ non-vacuous lift to T² (sig (1,1))
  - `HodgeRiemannT2.lean`   — ★ Kähler class on T² with cup>0

### Kähler 2-fold cases (4)
  - `HodgeIndexP2.lean`         — ℙ² (1, 0)
  - `HodgeIndexP1Squared.lean`  — ℙ¹×ℙ¹ (1, 1)
  - `HodgeIndexT2Squared.lean`  — ★ T²×T² sig (3, 3)
  - `HodgeRiemannT2Squared.lean`— ★★★ HR ℚ-positivity refinement on
                                  P^{1,1} ⊂ T²×T²

### Comparison + Hirzebruch (3)
  - `SurfaceComparisonTheorem.lean` — 4-fold cross comparison
  - `HirzebruchMultiplicative.lean` — Hirzebruch multiplicativity
  - `TensorSignature.lean`          — ★★★ Künneth pair-level

### T²ⁿ pattern + genus-g (3)
  - `T2nPattern.lean`     — ★★ pattern signature(H^n; T²ⁿ) = (½·C(2n,n), …)
  - `T2nInductive.lean`   — ★★★ G14 full inductive form, all n≥1
  - `GenusGSurface.lean`  — ★★★ Σ_g signature (g, g)

### Triple products (2)
  - `TripleProductSurface.lean`            — triple product surface
  - `TripleProductSurfaceParametric.lean`  — parametric variant

### Grade structure + balanced (5)
  - `HodgeIndexGradeStructure.lean`        — grade-aware HIT
  - `KahlerGradeStructure.lean`            — grade-aware Kähler
  - `BalancedSignature.lean`               — balanced (p,p) signature
  - `ProductSurfaceSignature.lean`         — product-surface signature
  - `SignatureMetaTheorem.lean`            — meta-level statement

## Pattern (∅-axiom)

  `signature(H^n; T²ⁿ) = (½·C(2n, n), ½·C(2n, n))`

  n=1: (1,1)   n=2: (3,3)   n=3: (10,10)   ...

Closed by `T2nInductive` for all n ≥ 1.

## Top-level

  - `Pairing.lean` aggregator — see for full per-file docstring

## Axiom status

★★★ marked files = STRICT ∅-AXIOM.  See per-file docstrings for
details.

## Where to add new files

  - New Kähler surface       → `HodgeIndex<name>` / `HodgeRiemann<name>`
  - Pattern extension        → `T2n*` / `GenusG*`
  - Künneth / multiplicative → `TensorSignature` / `Hirzebruch*`
  - Triple-product variants  → `TripleProduct*`
