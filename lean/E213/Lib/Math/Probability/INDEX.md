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

## Synthesis

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Capstone.lean` | per-cluster witnesses + `total_witness` (20-fact bundle) | 6 | ∅-axiom |
| `Probability.lean` | umbrella | — | — |

**Total**: 108 atomic facts, all ∅-axiom verified.

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

  * **`total_witness`** ★★★ — 20-fact grand bundle (4 per cluster).

## Open follow-ups (deferred)

  * Cauchy-modulus full CLT via `Real213.CutSeries.partialSum`.
  * Beta density on dyadic [0, 1] (continuous form requires the
    deferred Real213 integration step).
  * Hoeffding-style atomic concentration bounds.
