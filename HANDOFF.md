# Session Handoff — 2026-06-18

## Branch
`claude/multi-agent-math-research-n68ovi` — all pushed; **merged `origin/main`
in** (the `frontier-research-agents` work now fully contained). Full Math
builds clean (`lake build E213.Lib.Math` → 1936 modules).

## Scope
Math-only marathon (physics excluded by standing directive — it follows once
the math is complete). Multi-agent: parallel general-purpose subagents on deep
∅-axiom targets, each verified PURE in isolated scratch, ported into the corpus.

## Forcing-PURE leg (current — "forcing vs bookkeeping" selector)

Per the originator's reframe ("본질적으로 뭘까" → collect theorems where requiring
∅-axiom *forces a structurally different, revealing proof*, not bookkeeping):
running collection `research-notes/frontiers/pure_forces_different_proof.md`;
permanent chapter `theory/meta/forcing_versus_bookkeeping.md`. New this leg:

> **Session running total: ~49 ∅-axiom modules + the `exists_collision` primitive
> (now reused in 5 distinct theorems: DividesPair, TwoSquare, ErdosSzekeres,
> Pisano, ConsecutiveSumDvd), all PURE, full Math green at 2002.** Two complete classical arcs closed
> end-to-end: **Euler's theorem** (`EulerTheorem`) and the **Fermat–Gauss
> two-square characterization** (`TwoSquareTheorem` + `SumTwoSquaresCharacterization`
> + `InertPrimeThreeMod4` + `SumTwoSquaresOddPower` + `SumTwoSquaresBiconditional`,
> `isSumTwoSqNat_iff_even_vp`). Comprehensive constructive-analysis ledger
> (force-the-modulus: EVT/UniformLimit/Banach/Riemann/Cesaro/ModulusConvergence/
> LimitArithmetic/SqueezeProduct/**AlternatingSeries**; calibrations: BW→LPO,
> HeineCantor→fan, Dini→fan, real-decision quartet sign/equality/apartness/
> comparability ↔ LLPO/WLPO/MP). Units thread capped by **`WilsonGeneralization`**
> (29 PURE, `units_prod_eq_selfinv_prod` — Wilson's ±1 as the inverse-involution
> fixed-point product). Fresh recurrence thread: **`PisanoPeriod`**
> (Fibonacci mod m periodic, period = computed collision gap, backward via ℤ/m
> cancellation). **`ConsecutiveSumDvd`** (a consecutive run sums ≡0 mod n,
> computed). Fibonacci-mod-m sub-arc complete (PisanoPeriod + PisanoPeriodMinimal + FibonacciApparition: rank of apparition, zeros = its multiples). FTA complete (PrimeFactorization existence + FTAUniqueness: multiplicity = vp q n). Inequality sub-arc: Cauchy–Schwarz + Chebyshev (computed slack). Cauchy–Schwarz via Lagrange (slack = computed cross-square sum). Recent combinatorics: Redei (tournament Ham path), Mirsky (poset antichain cover via computed height), ConsecutiveSumDvd; analysis: AlternatingSeries, ComparisonTest, LimitArithmetic, SqueezeProduct. RESEARCH RESULT — the Wilson ±1 VALUE DICHOTOMY complete: ∏ units ≡ −1 ⟺ only ±1 are √1 (WilsonValue), ≡ +1 ⟺ ∃ nontrivial √1 (WilsonPlusOne — a NOVEL ∅-axiom argument P≡t^(|S|/2)+parity, no group theory, worked out then verified). + SqrtOnePrimePower/SqrtOneTwoPrimePower (−1 keystones) + WilsonExistence (+1 via CRT crtSolve(1,−1) / 2^a witness). Residual: only the finicky n-factorization case-split for the full ⟺ n∈{1,2,4,pᵏ,2pᵏ} (routine). Honest rejection: disc-8 x²+2y² Thue proof (rep_of_mod8 already exists). Open frontiers: `hall_general_induction`,
> `analysis_modulus_pending` (product/squeeze done; abstract additive-metric only).
- **`NumberTheory/UnitsOfZn`** (12 PURE, vein A) — `(ℤ/n)^×` on representatives:
  unit = coprime residue, closure = gcd fact, inverses = Bezout, order = φ(n)
  (`unit_count_eq_totient := rfl`). Quotient ring was packaging.
- **`NumberTheory/DividesPairPigeonhole`** (7 PURE, vein B) — n+1 in [1,2n] ⟹
  one divides another; dividing pair computed from v2 comparison.
- **`Combinatorics/Pigeonhole.exists_collision` / `exists_collision_lt`** (PURE)
  — NEW reusable primitive: constructive collision-*producing* pigeonhole
  (returns the pair via decidable `scan` + `shiftAround`), where `no_inj_lt`
  only refuted injectivity. The witness-returning form is pigeonhole's
  constructive content.
- **`NumberTheory/TwoSquareTheorem`** (19 PURE, vein B capstone) — Fermat's
  two-square theorem, hard direction (`p ≡ 1 mod 4 ⟹ p = a²+b²`), FULL incl.
  descent to `a²+b² = p`. All non-constructive content localized to
  `exists_collision_lt` (the Thue box collision). Reuses `QRNegOne`, `IntSqrt`,
  `PolyRoot` Nat↔Int bridges, `Int213`.
- **`NumberTheory/FermatQuartic`** (29 PURE, vein B capstone) — `x⁴+y⁴≠z²` (and
  `≠z⁴`), FULL descent. Classical minimal-counterexample → explicit `strongRecOn`
  on `z` whose step *constructs* the smaller solution (two Pythagorean-converse
  inversions + coprime-square split returning `a=√r,b=√s,c=√(r²+s²)`). Built the
  missing `pyth_converse` (Pythagorean converse over Nat). Nat-native.
- **`NumberTheory/PrimesThreeModFour`** (14 PURE, vein B) — infinitely many
  primes ≡3 mod 4, `∀ N, ∃ p, N<p ∧ prime p ∧ p%4=3`. Computed Euclid witness
  (least ≡3-mod-4 prime factor of `4·N!−1`); keystone `exists_prime_factor_3mod4`
  by least-factor recursion. No finite-list contradiction.
- **`Combinatorics/ErdosSzekeres`** (29 PURE, vein B, FRESH domain) — monotone
  subsequence via the `(inc,dec)` label-box `exists_collision_lt`; explicit
  subsequence extracted choice-free (`inc_subseq`). Third `exists_collision`
  reuse — broadens beyond number theory.
- **`NumberTheory/TotientMultiplicative`** (20 PURE, vein A) — `totient_mul`:
  φ(mn)=φ(m)φ(n) coprime, via the explicit CRT counting bijection. **Closes the
  leg's own loop**: built on `UnitsOfZn` + `CRTReconstruction` (this leg). CRT
  iso = reconstruction algorithm; φ-mult = Fubini reindex of the coprimality
  indicator. (Recovered from a watchdog-stalled agent — core was complete in
  scratch.)

Meta-finding crystallized in the chapter: **a primitive can be a
non-constructivity sink** — `exists_collision` localizes the sole non-constructive
step of THREE classical theorems (DividesPair, TwoSquare, ErdosSzekeres); the
named primitive, not the individual theorems, is the deliverable.

Honest rejection: √2/√p irrationality by v2-parity — the bare impossibility is
already PURE in `Irrational/SqrtPure` (via descent); a reproof is a duplicate
result, not a forcing case.

### Analysis sub-arc (answering "do the things that look impossible ∅-axiom")
On the directive to tackle continuity/limits/analysis — the domains classically
tied to LEM/compactness/choice. Answered symmetrically (vein C), four cases:
- **`Analysis/ExtremeValue`** (23 PURE) — EVT modulus form: sup VALUE computable
  (`CauchyCutSeq.limit` + convergence modulus), located/approached, attained at
  every finite resolution, but the maximizer `max_reached_by_none` (the argmax
  moves with resolution — analysis-level `object1_not_surjective`). Unconditional.
- **`Analysis/UniformLimitContinuous`** (20 PURE) — uniform limit of continuous is
  continuous: the limit's modulus *computed* `Ω m = ω_{r(m+2)}(m+2)`. Unconditional.
- **`Logic/BolzanoWeierstrass`** (13 PURE) — binary BW *calibrated*: `lpo_of_bw`
  (BW ⟹ LPO); `bw_of_lpo` at plain LPO NOT provable (extraction is Π⁰₂, above the
  ledger). The import named (LPO) and measured (Π⁰₂), not removed.
- **`Logic/HeineCantor`** (10 PURE) — HC *calibrated* to the fan theorem:
  `heineCantor_of_fan`, the fan theorem the load-bearing `Bar → Bounded` bridge.
- **`Logic/Dini`** (14 PURE) — Dini's theorem *calibrated* to the fan theorem
  (sibling of HeineCantor); monotonicity turns the per-interval bound into a
  uniform convergence index. `dini_of_fan`.
- **`Logic/RealDichotomyLLPO`** (31 PURE) — the **analytic-LLPO** calibration,
  two-sided: the real sign-dichotomy `∀ x, x≤0 ∨ 0≤x` IS LLPO
  (`llpo_of_realDichotomy` + converse). Locates exactly why the *exact* IVT /
  bisection sign step can't be ∅-axiom (it's LLPO) while the corpus's *approximate*
  IVT (`cutEq … 0`) stays pure. The encoding's "denominator blow-up" is the
  omniscience cost made visible. The deepest analysis calibration.
- **`Analysis/BanachFixedPoint`** (12 PURE) — Banach contraction fixed-point,
  modulus form: Picard iterates Cauchy with computed geometric modulus `N(m)=m`
  (`picard_cauchy`); fixed point the Cauchy limit, located + unique. Completeness
  as data+spec (`CompleteMetricModulus`), not an existence miracle. Reuses this
  session's own `MetricModulus`. Unconditional.
- **`Logic/RealEqualityWLPO`** (16 PURE) + **`Logic/RealApartnessMP`** (15 PURE) —
  the **real-decision triad** with `RealDichotomyLLPO`: sign ⟺ LLPO, equality ⟺
  WLPO, apartness ⟺ MP (mirrors `lpo_iff_wlpo_and_mp` at the real level). The
  negation is free; the disjunctive verdict is LLPO/WLPO; locating the apartness
  witness is MP (a bounded search the located bound makes terminate). Both
  two-sided.

The symmetry (now NINE analysis cases): **EVT + UniformLimit + Banach force the
hidden modulus; BW + HeineCantor + Dini + the real-decision triad
(RealDichotomyLLPO/RealEqualityWLPO/RealApartnessMP) name and measure the import**
— a reverse-math ledger across the LPO / WLPO / MP / LLPO / fan rungs. 213 never
smuggles an exterior. Logged in the frontier collection + the methodology
chapter's vein-C section. Full Math green at **1972 modules**.

### Tier-C continuation (autonomous marathon, post-triad)
- **`Analysis/RiemannContinuous`** (9 PURE) — continuous ⟹ Riemann integrable,
  convergence modulus *computed* from the u.c. modulus (`riemannSum_cauchy`);
  integral = explicit Cauchy limit. Reuses `MetricModulus` + `CutRiemann`.
- **`Combinatorics/HallMarriage`** (36 PURE) — Hall's matching produced as DATA
  (scan returns the right vertex; Hall = the scan never fails). Closed: framework
  + counting infra + computed `hall_matching_{zero,one,two}`. General-`n`
  (Halmos–Vaughan) is OPEN → `frontiers/hall_general_induction.md`; an agent is
  currently attempting it (scratch `ScratchHG`). Full Math green at **1974**.
- **`Analysis/ModulusConvergence`** (6 PURE) — limit theory on `MetricModulus`:
  `limit_unique` (located-unique limit, ∀m close m L L'), `conv_imp_cauchy`
  (Cauchy modulus computed from convergence modulus), `subseq_converges`,
  `const_converges`. Done directly (not via agent).
- **`Analysis/CesaroMean`** (16 PURE) — Cesàro convergence, averaging modulus
  computed `Nstep m = N + 2^m·E + 1` (`E` = early-term spread); `closeAvg` is the
  multiplied-out `Nat` inequality (no division). Pure-twin `NatHelper.add_mul`.
- **`Logic/RealComparabilityLLPO`** (2 PURE) — general real comparability
  `∀ x y, x≤y ∨ y≤x ⟹ LLPO` (reals not constructively totally ordered); one-liner
  over `RealDichotomyLLPO`.
- **`Analysis/LimitArithmetic`** (12 PURE) — sum limit law on `distMet`:
  `distN_add_le` + `add_converges` (modulus `max(ra(m+1),rb(m+1))`) + `shift`.
- **`Analysis/SqueezeProduct`** (8 PURE) — `squeeze_converges` (a≤c≤b, a,b→L ⟹
  c→L) + `mul_converges_bounded` (product, modulus shifted by bit-length
  `floorLog 2 K + 1`). The limit-law thread (sum/product/squeeze/Cesàro/
  uniqueness/Cauchy) is now comprehensive.
- **Two-square arc COMPLETE** (∅-axiom, all computed modular facts, no ℤ[i]):
  `TwoSquareTheorem` (hard dir) + `SumTwoSquaresCharacterization` (18 PURE, the
  "if" direction via the Brahmagupta product) + `InertPrimeThreeMod4` (7 PURE,
  the "only if" core) + `SumTwoSquaresOddPower` (15 PURE, `even_vp_three_mod4`:
  a sum of two squares has even q-adic valuation at every q≡3mod4 — the inert-prime
  descent on `vp`). **Characterization CLOSED both directions**
  (`frontiers/two_square_only_if.md` → closed). Full Math green at **1982**.

**Orchestration lesson (for next iteration):** the env cleans agent scratch dirs
between Bash calls, which RACES any "scratch removed ⟹ done" watcher and gives
false "no checkpoint" reads (Cesàro + LimitArithmetic both *succeeded* but read as
misses first). Reliable signal = the agent's own completion notification (it
carries the report + checkpoint path); re-check `/tmp/<tag>/Result.lean` after the
notification, not on scratch-dir poll.

### Open frontiers (next-iteration targets — recorded per PROCESS frontier rule)
- `frontiers/hall_general_induction.md` — Hall general-`n` (Halmos–Vaughan);
  framework + n≤2 closed in `Combinatorics/HallMarriage`; remaining = `Fin`
  subgraph re-indexing after vertex+neighbor deletion. (An agent attempt left no
  PURE checkpoint — the reindexing is the genuine hard part.)
- `frontiers/analysis_modulus_pending.md` — Cesàro mean, limit-arithmetic
  (sum/product need an *additive* metric beyond `MetricModulus`), squeeze. Do
  **directly**, not via one-shot agent — the obstruction is pure-`Nat`-inequality
  propext-avoidance, handled interactively with `NatHelper`/`PureNat` twins (as
  `ModulusConvergence` just demonstrated).
- Other unselected: fan ⟺ WKL relationship; exact-IVT⟺LLPO (the function-family
  version, beyond the dichotomy); EGZ / Dilworth / Mirsky (combinatorics).

Full `E213.Lib.Math` green at **1967 modules**; all pushed. Leg total: **11
modules + the `exists_collision` primitive**, ∅-axiom PURE — 7 number-theory/
combinatorics (12+7+19+29+14+29+20) + 4 analysis (23+20+13+10).

## Post-merge continuation (after merge-to-main; second marathon leg)
Elementary classical number theory + combinatorics, all ∅-axiom PURE:
- **Euler's theorem** `EulerTheorem.euler_theorem`: `a^φ(n) ≡ 1 (mod n)`, all
  n≥2, coprime a (39 PURE) — Route B (totative-product permutation + unit
  cancellation; Route A rejected as circular for composite n). HEADLINE.
- **Multiplicative order** `MultiplicativeOrder.{ord, ord_dvd_of_pow_one,
  ord_dvd_totient}`: ord divides φ(n) for COMPOSITE n (26 PURE) — generalizes
  the corpus's prime-only MulOrder, Euler-enabled.
- **Multiplicative-function structure** (the family-level theorems):
  `SummatoryMultiplicative.summatory_mul` (f mult ⟹ Σ_{d∣n}f(d) mult),
  `DirichletMultiplicative.dconv_mul` (f,g mult ⟹ f∗g mult — Dirichlet-ring
  capstone), `MultiplicativeUniqueness.mult_eq_of_prime_pow` (determined by
  prime-power values), `SquareValuation.isSquare_iff_all_vp_even` (general
  square char, frontier crux #2 all-primes), `LiouvilleValuation.lambdaV_*`
  (completely-multiplicative λV, general divisor-sum=[square]).
- **Totient pairing** `TotientPairing.{totient_even (φ(n) even, n≥3),
  sum_totatives (2Σ=nφ), gcd_reflect}` (18 PURE).
- **Combinatorics** `BinomialInversion.{binomial_orthogonality,
  binomial_inversion}` (39 PURE), `SurjectionCount.{surj_zero_of_lt,
  surj_diag}` + a fresh finite-difference machinery (`A_rec`, `PolyLe`
  degree theory) (44 PURE).
The multiplicative_divisor_theory.md chapter was updated (§2.5 structural
theorems, §3/§7 generalizations).
- **Valuation arc**: `LegendreDePolignac` (Legendre recurrence + de Polignac
  digit-sum `(p−1)·vp_p(n!)+s_p(n)=n`, 15 PURE) → `KummerTheorem`
  (`(p−1)·vp_p(C(m+n,m)) = s_p(m)+s_p(n)−s_p(m+n)` = base-p carry count, 7 PURE).
- **Set-partition combinatorics cluster** (promoted to
  `theory/math/combinatorics/inclusion_exclusion_set_partitions.md`):
  `BinomialInversion` (39), `SurjectionCount` (44, + a fresh finite-difference
  machinery `A_rec`/`PolyLe`), `DerangementInclusionExclusion` (11),
  `StirlingExplicit` (`surj=n!·S`, 13), `BellStirling` (`B_n=Σ_k S(n,k)` general
  + the block-conditioning identity, 10).
- **Order theory (new `Lib/Math/Order/` cluster — fresh domain pivot)**:
  `GaloisConnection` (unit/counit, monotonicity, triangle identities, the g∘f
  closure operator; multiply/divide adjunction witness, 15 PURE),
  `BooleanAlgebra` (Huntington axioms ⟹ complement uniqueness, double-complement,
  both De Morgan laws; Bool instance, 25 PURE), `KnasterTarski` (lfp/gfp
  fixed-point theorem on a parametrized complete lattice, 19 PURE).

## What Was Done This Session (first leg, before merge)

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
