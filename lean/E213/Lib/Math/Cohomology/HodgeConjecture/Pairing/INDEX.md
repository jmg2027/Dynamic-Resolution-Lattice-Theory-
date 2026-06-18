# `Lib/Math/Cohomology/HodgeConjecture/Pairing/` — surface intersection forms

Cup-product pairings and their signatures on real CW surfaces:
Hodge Index signatures and the signed-ℤ Hodge–Riemann polarization,
on Kähler 2-folds (T², ℙ², ℙ¹×ℙ¹, T²×T²) and parametric
generalisations.

## Files (18)

### T² + signed HR (2)
  - `HodgeRiemann.lean`     — signed-ℤ HR polarization (Q, J),
                              positive-definite `h = Q·J = I`
  - `HodgeIndexT2.lean`     — ★ T² (sig (1,1))
  - `HodgeRiemannT2.lean`   — ★ Kähler class on T² with cup>0

### Kähler 2-fold cases (4)
  - `HodgeIndexP2.lean`         — ℙ² (1, 0)
  - `HodgeIndexP1Squared.lean`  — ℙ¹×ℙ¹ (1, 1)
  - `HodgeIndexT2Squared.lean`  — ★ T²×T² sig (3, 3)
  - `HodgeRiemannT2Squared.lean`— ★★★ HR ℚ-positivity refinement on
                                  P^{1,1} ⊂ T²×T²

### Comparison + Künneth (2)
  - `SurfaceComparisonTheorem.lean` — 4-fold cross comparison
  - `TensorSignature.lean`          — ★★★ Künneth pair-level

### T²ⁿ pattern + genus-g (3)
  - `T2nPattern.lean`     — ★★ pattern signature(H^n; T²ⁿ) = (½·C(2n,n), …)
  - `T2nInductive.lean`   — ★★★ G14 full inductive form, all n≥1
  - `GenusGSurface.lean`  — ★★★ Σ_g signature (g, g)

### Triple products (2)
  - `TripleProductSurface.lean`            — triple product surface
  - `TripleProductSurfaceParametric.lean`  — parametric variant

### Grade structure + balanced (4)
  - `HodgeIndexGradeStructure.lean`        — grade-aware HIT
  - `KahlerGradeStructure.lean`            — grade-aware Kähler
  - `BalancedSignature.lean`               — balanced (p,p) signature
  - `ProductSurfaceSignature.lean`         — product-surface signature

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
  - Künneth / multiplicative → `TensorSignature`
  - Triple-product variants  → `TripleProduct*`
