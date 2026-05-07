# Probability 213 — Module Index

Blueprint: `blueprints/math/01_probability_213.md`.

## Atomic foundations

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Cut.lean` | `ProbabilityCut` (mass `num/den`) | 10 | 10/10 ∅-axiom |
| `UniformOnUnit.lean` | `UnitSubBracket` + `uniform` | 5 | 5/5 ∅-axiom |
| `Bernoulli.lean` | two-outcome, `success + failure = 1` | 9 | 9/9 ∅-axiom |
| `Binomial.lean` | K_{3,2} pair + n-trial product mass | 13 | 13/13 ∅-axiom |

## Expectation + variance

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Expectation.lean` | Bernoulli `E[X] = p`, discrete weighted sum | 11 | 11/11 ∅-axiom |
| `Variance.lean` | Bernoulli `Var[X] = p(1−p)`, second moments | 12 | 12/12 ∅-axiom |

## Sample mean + Law of Large Numbers

| File | Topic | Theorems | Status |
|---|---|---|---|
| `SampleMean.lean` | `countTrue`, all-heads/tails closed form, `length_replicate` | 11 | 11/11 ∅-axiom |
| `LLN.lean` | balanced sequence sample mean = E[X], `LLN_unit`, fair-coin LLN | 8 | 8/8 ∅-axiom |

## Bayesian conjugate update

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Bayesian.lean` | `BetaCount` + `posteriorMean` + Laplace + sequential↔batch | 14 | 14/14 ∅-axiom |

## CLT + Gaussian peak

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Gaussian.lean` | `expSumAtZero = 1`, peak = 1, CLT centering / variance | 9 | 9/9 ∅-axiom |

## Independence + conditional

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Independence.lean` | `joint a b` (product mass), `conditionalNum`/`Den`, comm + identity laws | 12 | 12/12 ∅-axiom |

## Markov / sufficient statistic

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Markov.lean` | `BetaCount` update commutativity (Markov property) + atomic Markov inequality on discrete distributions | 6 | 6/6 ∅-axiom |

## Concentration bounds

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Concentration.lean` | `excess` / `deficit` clamped-Nat, `centeredAbsDev2`, balanced/all-heads/all-tails closed forms | 7 | 7/7 ∅-axiom |

## Beta density (continuous)

| File | Topic | Theorems | Status |
|---|---|---|---|
| `BetaDensity.lean` | unnormalized `betaNumAt α β p`, `betaDenAt`; Beta(1,1) uniform, Beta(2,1) linear; bridge from `BetaCount` | 8 | 8/8 ∅-axiom |

## CLT modulus (Cauchy form)

| File | Topic | Theorems | Status |
|---|---|---|---|
| `CLTLimit.lean` | balanced LLN as Cauchy sequence with trivial modulus `N(ε) = 0` | 4 | 4/4 ∅-axiom |

## Real213 extension program (PR #?, branch `claude/probability-real213-extensions`)

| File | Topic | Theorems | Status |
|---|---|---|---|
| `CauchyModulus.lean` | `ProbCauchy` record + `absDevCross` + `constSeq_cauchy` + balanced bridge | 6 | 6/6 ∅-axiom |
| `RiemannBridge.lean` | width-scaled Riemann + propext-clean rebuild of bracket Cauchy modulus (`one_le_two_pow`, `succ_le_two_pow`, `convergence_modulus_const`) | 8 | 8/8 ∅-axiom |
| `Chebyshev.lean` | polynomial concentration via `Markov.markov_inequality` | 5 | 5/5 ∅-axiom |
| `BetaNormalized.lean` | closed-form `B(α,β) ∈ {(1,1),(2,1),(1,2)}` integrals | 11 | 11/11 ∅-axiom |
| `CLTGeneric.lean` | variance-modulus `cltModulus_of_varBound V ε := V·ε` + balanced collapse | 7 | 7/7 ∅-axiom |
| `Real213/CutFactorial.lean` | `factorial`, `cutInvFactorial`, term-mode `factorial_pos` | 10 | 10/10 ∅-axiom |
| `Real213/CutExpSeries.lean` | `expTerm`, `expPartialSum`, `cutExp` skeleton; rfl-level witnesses | 7 | 7/7 ∅-axiom |
| `Real213/CutExpODE.lean` | discrete ODE recurrence (`f(N+1) = f N + expTerm N`) | 2 | 2/2 ∅-axiom |
| `Hoeffding.lean` | finite-depth Taylor exponential bound + balanced collapse | 5 | 5/5 ∅-axiom |

## Synthesis

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Capstone.lean` | per-cluster witnesses (atoms / moments / sampleMean / bayesian / gaussian / independence / markov / concentration / betaDensity / cltModulus / **cauchyModulus** / **chebyshev** / **betaNormalized** / **cltGeneric** / **hoeffding**) + `total_witness` | 16 | ∅-axiom |
| `Probability.lean` | umbrella | — | — |

**Total**: 217 atomic facts, all ∅-axiom verified (156 prior + 61
from Real213 extension program; 5 new capstone witnesses).

## Atomic content

  * **Mass**: `(num, den)` with `0 < den ∧ num ≤ den` — Bishop-style
    rational in `[0, 1]`.  Embeds into `FluxCut` as forward = `num/den`,
    backward = `0/1`.

  * **Uniform**: dyadic sub-bracket `[a/2^E, b/2^E]` carries
    mass `(b−a)/2^E`.  No integration step — just structural data.

  * **Bernoulli**: `success.num + failure.num = den` via
    `Nat213.add_sub_of_le`.  Atoms: `fair` (1/2), `certain`, `impossible`.

  * **Binomial / K_{3,2}**: 10-pair categorical `3 + 1 + 6 = 10`
    lifted from `Physics.Substrate.Pairs`.  Bernoulli view: `ABBernoulli`
    with `p = 6/10`, `failure = 4/10`.  Product mass for `n` independent
    trials via `trialSequenceNum`.

  * **Expectation**: `E[X] = success.num / den` (Bernoulli direct);
    `discreteNum` for list-form weighted sums; K_{3,2} expectation
    `13/10`; AB-indicator expectation `6/10`.

  * **Variance**: `Var[X] = success · failure / den²`;
    `bernoulliNum b = num · (den − num)` (rfl); fair-coin `1/4`;
    AB-indicator `24/100`; second-moment list helper.

  * **Sample mean**: `sampleMeanNum xs = countTrue xs`,
    `sampleMeanDen xs = xs.length`.  All-heads / all-tails / balanced
    closed forms.  213-native `length_replicate` + `length_append`
    (Lean-core variants leak `propext`).

  * **`LLN_unit`** ★ — balanced fair-coin sample of length `2n` has
    sample mean *exactly* `1/2` for every `n` (no limit needed).
    `bernoulli_LLN_exact` — empirical = theoretical → `sampleMean = E[X]`
    by cross-multiplication.

  * **Bayesian**: `BetaCount (α, β)` with `0 < α + β`;
    `posteriorMean = α / (α + β)` as `ProbabilityCut`.
    `updateOnSuccess` / `updateOnFailure` are `+1` on the matching
    field; `updateBatch ks fs` does both.  Laplace rule of succession:
    `uniformPrior = (1, 1)` → `1/2`, after one success → `2/3`,
    after one failure → `1/3`.  Sequential ↔ batch via `Nat` add
    associativity.

  * **Gaussian peak**: `expTaylorAtZero` → only `n = 0` term survives.
    `expSumAtZero N = 1` ★ for every `N` (induction adds `0`).
    Gaussian peak `exp(−0²/2) = 1`.

  * **CLT centering**: balanced fair-coin length-`2n` has
    `2 · countTrue = length` exactly (zero deviation, attained
    structurally).  `CLT_fair_variance_marker` matches Bernoulli
    `Var = 1/4`.

  * **Independence**: `joint a b` is the *product mass* —
    numerator and denominator factorize.  Joint with `unit` is
    identity, joint with `zero` is `zero`.  Commutative.
    `conditionalNum a b = a.num`, `conditionalDen a b = b.num` —
    the atomic ratio form of `P(A | B)` at common scale.

  * **`total_witness`** ★★★ — 20-fact grand bundle (4 per cluster
    of the original five clusters).

## Open follow-ups (after Real213 extension)

All originally-deferred items now have at least atomic ∅-axiom
witnesses:

  * ✅ Cauchy-modulus form of LLN — `CLTLimit.lean` + `CauchyModulus.lean`.
  * ✅ Beta density on dyadic — `BetaDensity.lean` (unnormalized) +
    `BetaNormalized.lean` (closed-form `(1,1)`, `(2,1)`, `(1,2)`).
  * ✅ Concentration bounds — `Concentration.lean` + `Chebyshev.lean`
    (polynomial substitute) + `Hoeffding.lean` (finite-depth
    exponential, with `cutExp` Taylor skeleton).
  * ✅ Markov property + sufficient statistic — `Markov.lean`.
  * ✅ Generic CLT — `CLTGeneric.lean` (variance modulus).
  * ✅ `cutExp` transcendental layer — `Real213/CutExpSeries.lean`
    (Taylor) + `Real213/CutExpODE.lean` (discrete ODE recurrence).

Remaining genuine gaps (separate marathon territory):

  * Full Cauchy convergence modulus for `cutExp` partial sums on
    `x ≠ 0` — requires geometric-majorant ratio test on
    `partialSum`'s upstream.
  * Continuous Chernoff `inf_t` over real-valued `t` (finite-grid
    approximation feasible with explicit error bound).
  * `Real213.log` for symmetric tightness bounds.
