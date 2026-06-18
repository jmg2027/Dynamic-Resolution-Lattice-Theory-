# Session Handoff — 2026-06-18

## Branch
`claude/frontier-research-agents-h5okq9` — pushed, **87 commits ahead of `origin/main`, 0 behind**
(main fully contained).  Authoritative build `cd lean && lake build E213` → **green** (435 modules;
`E213.Lib` 1685 files).  Strict ∅-axiom intact: every theorem added is `#print axioms`-empty.

## What Was Done This Session

A long autonomous research marathon followed by a structured close-out (process → promotion →
cross-domain → essay → org-audit → purity → ready-to-merge → handoff).

### 1. Lifting-the-Exponent — FULLY CLOSED ∅-axiom (headline)
`LiftingExponentGeneral.lte` : `v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)` for an odd prime `p` (`3 ≤ p`),
`p ∣ (a−b)`, `p ∤ b`, `b < a`, `n ≥ 1`.  Proof stack (all PURE):
- `BinomialTwoVar.add_pow` — two-variable binomial theorem `(b+d)ⁿ = Σ C(n,k) b^{n−k} dᵏ` (repo had
  only the `b=1` `binomSum`; this was the missing infra).
- `LiftingExponentPP.{vp_add_eq_min, dvd_sumTo, le_vp_sumTo}` — ultrametric strict-min law + tail bound.
- `LiftingExponentMain.lifting_prime_power` — kernel `v_p(aᵖ−bᵖ)=v_p(a−b)+1` (binomial route).
- `LiftingExponentCoprime.lifting_coprime` — `v_p(aᵐ−bᵐ)=v_p(a−b)` for `p∤m`.
- `LiftingExponentGeneral.{vp_pow_pk, lte}` — iterate kernel + factor `n=pᵏ·m`.
- Promoted to `theory/math/numbertheory/lifting_the_exponent.md`.

### 2. σ_m (divisor-power sum) — fully closed
`SigmaPrimePowGeom` + `SigmaDivisorClosed`: prime-power closed form `(pᵐ−1)σ_m(pᵏ)=p^{m(k+1)}−1`,
and `divisorSumZ_mul_of_completely_mult` (the reusable general law: divisor-sum multiplicativity for
*any* completely-multiplicative weight — σ/τ/σ_m all corollaries).  Promoted as §8 of
`theory/math/numbertheory/multiplicative_divisor_theory.md`.

### 3. Euclidean lattice metric geometry — new cluster
`StewartTheorem` (Stewart, Apollonius), `MetricIdentities` (British-flag, parallelogram, Pythagoras,
Leibniz centroid, Euler quadrilateral), `LatticeArea` (shoelace, signed-area additivity/symmetry,
2D Lagrange, law of cosines, **Cayley–Menger**, SL₂(ℤ) area invariance).  Integer `sq`/`area2`, all
`ring_intZ`/`decide`.  Promoted to `theory/math/geometry/euclidean_lattice_metric.md`.

### 4. Combinatorics + factorization
Hockey-stick identity (`HockeyStick`), binomial-mean `Σ k·C(m,k)=m·2^{m-1}` (`BinomialMean`),
homogeneous power-difference factorization (`PowSubPowFactor`), ℤ cofactor congruence
(`LiftingExponent`).

### 5. Close-out
- `/process`: decoupled 5 `lean/` docstrings from `research-notes/frontiers/` notes (sink rule → 0).
- `/promotion`: 3 promotions (LTE, σ_m §8, geometry) logged #93-95 in `promotion_essay_log.md`.
- cross-domain note `research-notes/frontiers/lte_geometry_crossdomain.md` (6 main×branch links).
- `/essay`: `theory/essays/synthesis/addition_and_multiplication_are_two_faces_of_one_count.md`
  (vp's additive face `vp_add_eq_min` = the dual of multiplicativity; logged #96).
- `/org-audit`: fixed one dated note in `theory/`; no orphans; new Lean docstrings clean.
- `/purity-check` + `/ready-to-merge`: passed (0 forbidden, full build green, 0 sink leaks).

## Current Precision Results (0 free parameters)
Unchanged this session — no physics-branch work.  See `catalogs/physics-constants.md` for the
constant/precision table; `STRICT_ZERO_AXIOM.md` for the PURE/DIRTY catalog.  This session's
additions are all pure-math (number theory / geometry / combinatorics), `#print axioms`-empty.

## Open Problems (Priority Order)

### 1. General Rolle / MVT over arbitrary differentiable functions
Current MVT is *witness-at* only (`FluxMVT.DyadicMVTWitness`, specific polynomials).  General Rolle
needs the extreme-value theorem over `Real213` (compactness on the cut algebra) — heavy multi-file
build, no missing ∅-axiom *ingredient*, just assembly.
Frontier note: `research-notes/frontiers/multi_agent_marathon_2026_06_16.md` ("Open frontier — general Rolle / MVT").

### 2. LTE at `p = 2`
The `p=2` variant (`v_2(aⁿ−bⁿ) = v_2(a−b)+v_2(a+b)+v_2(n)−1` for even `n`) is not formalized; the
strict-minimum face ties when the two least terms coincide.
Frontier note: same marathon note + `theory/math/numbertheory/lifting_the_exponent.md` "Scope / open edge".

### 3. Bertrand's postulate — final assembly
All component lemmas ∅-axiom (primorial keystone, binom/fact bridges, window-vanishing); remaining
is the prime-range partition + crossover inequality + finite chain.
Frontier note: `research-notes/frontiers/bertrand_postulate.md`.

### 4. Multiplicative-function abstraction
"Any multiplicative function's value forced by descent over the UFD vector" — `divisorSumZ_mul_of_completely_mult`
is a step; the full abstraction is open.
Frontier note: `research-notes/frontiers/multi_agent_marathon_2026_06_16.md` + the multiplicativity essay's open frontier.

## Unresolved from This Session
- `ring_intZ` performance ceiling: degree-8 multivariate (Cayley–Menger) times out directly —
  surmounted by abstract-atom decomposition, but the ceiling itself remains (a faster reflective
  normalizer would unlock higher-degree algebraic geometry directly).

## Next
Either (a) the `p=2` LTE variant (smaller, well-scoped), (b) Bertrand final assembly (item 3),
or (c) push the general Rolle/MVT (the one major untouched domain — heavy).

## Three-tier state
- **Promotions this session**: `theory/math/numbertheory/lifting_the_exponent.md` (new),
  `multiplicative_divisor_theory.md` §8 (append), `theory/math/geometry/euclidean_lattice_metric.md`
  (new) ← the LTE / σ_m / lattice-geometry Lean sub-trees.  Logged #93-96 in `promotion_essay_log.md`.
- **Promotion candidates**: Hockey-stick + Binomial-mean (`Combinatorics/`) — PURE, no chapter yet.
- **Active scratchpad**: `research-notes/frontiers/` (lte_geometry_crossdomain, marathon note).

## File Map
```
lean/E213/Lib/Math/NumberTheory/PowSubPowFactor.lean      ← homogeneous aⁿ−bⁿ factorization (ℤ)
lean/E213/Lib/Math/NumberTheory/LiftingExponent.lean      ← ℤ cofactor congruence (p∤exp core)
lean/E213/Lib/Math/NumberTheory/BinomialTwoVar.lean       ← two-variable binomial theorem
lean/E213/Lib/Math/NumberTheory/LiftingExponentPP.lean    ← ultrametric strict-min + sum bound
lean/E213/Lib/Math/NumberTheory/LiftingExponentMain.lean  ← prime-power kernel v_p(aᵖ−bᵖ)=v_p(a−b)+1
lean/E213/Lib/Math/NumberTheory/LiftingExponentCoprime.lean ← coprime case v_p(aᵐ−bᵐ)=v_p(a−b)
lean/E213/Lib/Math/NumberTheory/LiftingExponentGeneral.lean ← general LTE
lean/E213/Lib/Math/NumberTheory/SigmaPrimePowGeom.lean    ← σ_m prime-power geometric form
lean/E213/Lib/Math/NumberTheory/SigmaDivisorClosed.lean   ← σ_m divisor sum + general mult law
lean/E213/Lib/Math/NumberTheory/HockeyStick.lean          ← hockey-stick identities
lean/E213/Lib/Math/NumberTheory/BinomialMean.lean         ← Σ k·C(m,k)=m·2^{m-1}
lean/E213/Lib/Math/Geometry/StewartTheorem.lean           ← Stewart + Apollonius (sq)
lean/E213/Lib/Math/Geometry/MetricIdentities.lean         ← parallelogram/Pythagoras/Leibniz/Euler-quad
lean/E213/Lib/Math/Geometry/LatticeArea.lean              ← signed area, Cayley–Menger, SL₂(ℤ)
theory/math/numbertheory/lifting_the_exponent.md          ← NEW chapter (LTE)
theory/math/geometry/euclidean_lattice_metric.md          ← NEW chapter (lattice geometry)
theory/essays/synthesis/addition_and_multiplication_are_two_faces_of_one_count.md ← NEW essay
research-notes/frontiers/lte_geometry_crossdomain.md       ← cross-domain insights
research-notes/promotion_essay_log.md                     ← #93-96 appended
```
