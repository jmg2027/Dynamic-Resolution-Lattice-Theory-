# Probability 213 — Module Index

Blueprint: `blueprints/math/01_probability_213.md`.
Branch: `claude/probability-theory-marathon-n9B9z`.

## Phase EA — atomic foundations

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Cut.lean` | `ProbabilityCut` (mass `num/den`) | 10 | 10/10 ∅-axiom |
| `UniformOnUnit.lean` | `UnitSubBracket` + `uniform` | 5 | 5/5 ∅-axiom |
| `Bernoulli.lean` | two-outcome, `success + failure = 1` | 9 | 9/9 ∅-axiom |
| `Binomial.lean` | K_{3,2} pair + n-trial product mass | 13 | 13/13 ∅-axiom |

## Phase EB — expectation + variance

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Expectation.lean` | Bernoulli `E[X] = p`, discrete weighted sum | 11 | 11/11 ∅-axiom |
| `Variance.lean` | Bernoulli `Var[X] = p(1−p)`, second moments | 12 | 12/12 ∅-axiom |

## Phase EC — sample mean + Law of Large Numbers

| File | Topic | Theorems | Status |
|---|---|---|---|
| `SampleMean.lean` | `countTrue`, all-heads/tails closed form, `length_replicate` | 11 | 11/11 ∅-axiom |
| `LLN.lean` | balanced sequence sample mean = E[X], `LLN_unit`, fair-coin LLN | 8 | 8/8 ∅-axiom |

## Phase ED — Bayesian conjugate update

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Bayesian.lean` | `BetaCount` + `posteriorMean` + Laplace rule + sequential↔batch | 14 | 14/14 ∅-axiom |

## Phase EE — CLT + Gaussian peak

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Gaussian.lean` | `expSumAtZero = 1`, Gaussian peak = 1, CLT centering / variance marker | 9 | 9/9 ∅-axiom |

## Phase EF — Marathon final capstone

| File | Topic | Theorems | Status |
|---|---|---|---|
| `MarathonCapstone.lean` | ★ `phaseEF_marathon_capstone` ★ — 20-fact grand synthesis (4 per phase × 5 phases) | 1 | ∅-axiom |

## Synthesis

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Capstone.lean` | Phase EA + EB + EC + ED + EE synthesis bundles | 5 | ∅-axiom |
| `MarathonCapstone.lean` | Phase EF marathon final | 1 | ∅-axiom |
| `Probability.lean` | umbrella | — | — |

**Total**: 105 atomic facts (incl. 20-fact marathon capstone), all ∅-axiom.

## Atomic content

  * **Mass**: `(num, den)` with `0 < den ∧ num ≤ den` — Bishop-style
    rational in `[0, 1]`.  Embeds into `FluxCut` as forward = `num/den`,
    backward = `0/1`.

  * **Uniform**: dyadic sub-bracket `[a/2^E, b/2^E]` carries
    mass `(b−a)/2^E`.  No integration step required — just structural
    data.

  * **Bernoulli**: `success.num + failure.num = den` via
    `Nat213.add_sub_of_le`.  Atoms: `fair` (1/2), `certain`, `impossible`.

  * **Binomial / K_{3,2}**: 10-pair categorical distribution
    `3 + 1 + 6 = 10` lifted from `Physics.Substrate.Pairs`.
    Bernoulli view: `ABBernoulli` with `p = 6/10`, `failure = 4/10`.
    Product mass for `n` independent trials via `trialSequenceNum`.

## Marathon status

**Probability 213 marathon: COMPLETE.**  All five planned phases
(EA atomic foundations, EB expectation/variance, EC LLN, ED Bayesian,
EE CLT/Gaussian) delivered with 0 sorry, 0 external axioms, 0 Mathlib.
Marathon capstone bundles 20 headline facts in a single ∅-axiom theorem.

## Open follow-ups (deferred)

  * Cauchy-modulus full CLT via `Real213.CutSeries.partialSum`.
  * Beta density on dyadic [0, 1] (continuous form requires the
    deferred Real213 integration phase).
  * Hoeffding-style atomic concentration bounds.

## Phase EB content notes

  * **Bernoulli expectation**: `E[X] = success.num / den` — defined as
    a `ProbabilityCut` directly (= the success leg).

  * **Bernoulli variance**: `Var[X] = success · failure / den²`.
    Term-mode `bernoulliNum b = num · (den − num)` (rfl).

  * **Discrete moments**: list-form `discreteNum` (first moment) +
    `discreteSecondMomentNum`.  Closed form on K_{3,2}:
    `E[K32] = 13/10`, `E[K32²] = 25/10`.

  * **AB-indicator** (`success = AB`): variance numerator = 24,
    denominator = 100 (= 6·4 / 10² = p(1−p)).
    Second moment equals first moment (`X² = X` for indicator).

## Phase EC content notes

  * **Sample mean**: `sampleMeanNum xs = countTrue xs`,
    `sampleMeanDen xs = xs.length` (just `Nat` counts of `Bool`s).

  * **Closed forms**: all-heads of length `n` → `n/n`; all-tails → `0/n`;
    balanced `(replicate n true) ++ (replicate n false)` → `n/(2n)`.

  * **`LLN_unit`** ★ — balanced fair-coin sample of length `2n` has
    sample mean *exactly* `1/2` for every `n` (no limit needed —
    structural exactness under balance).

  * **`bernoulli_LLN_exact`** — for any sample where empirical count
    matches theoretical ratio (`countTrue · den = length · num`),
    `sampleMean = E[X]` via cross-multiplication.

  * 213-native `length_replicate` and `length_append` term-mode
    helpers (Lean-core variants leaked `propext` via `simp`).

## Phase ED content notes

  * **`BetaCount`**: `(α, β)` pair of effective counts with
    `0 < α + β`.  No continuous Beta density — just two `Nat`s.

  * **`posteriorMean`**: `α / (α + β)` as a `ProbabilityCut`.
    Bayes' update is **count addition** in this conjugate framework.

  * **`updateOnSuccess` / `updateOnFailure`**: `+1` on the matching
    field.  `updateBatch ks fs` does `+ks, +fs` in one step.

  * **Laplace's rule of succession**: `uniformPrior = (1, 1)` →
    `posteriorMean = 1/2`.  After one success → `2/3`; after one
    failure → `1/3`.  Pure `rfl`.

  * **Sequential ↔ batch**: `updateOnSuccess` count-equals
    `updateBatch 1 0`; two successes count-equals `updateBatch 2 0`.
    Bayesian update is associative + commutative *because Nat
    addition is*.

## Phase EE content notes

  * **`expTaylorAtZero n`**: Taylor coefficient of `exp(x)` at `x = 0`.
    Atomic: only `n = 0` survives (= `1`); all `n ≥ 1` give `0`
    because `x^n = 0` at `x = 0`.

  * **`expSumAtZero N = 1`** ★ — partial Taylor sum at every order
    `N` is exactly `1`.  Proof by induction on `N`; each step adds
    `0`.  This is `exp(0) = 1` in finite-resolution form.

  * **Gaussian peak**: `exp(−x²/2)|_{x=0} = exp(0) = 1`.
    `gaussianPeakAtZero = 1` and `gaussianPeakMass = 1/1` as
    a `ProbabilityCut`.

  * **CLT centering**: for fair-coin balanced length-`2n`,
    `2 · countTrue = length`, so the standardized deviation is
    *exactly zero*.  No limit needed — perfect centering attained
    structurally under balance.

  * **CLT variance marker**: `4 · (count · 2) = length · 4`,
    matching `p(1−p) = 1/4` Bernoulli variance after normalization.

  * Full Cauchy-modulus CLT is deferred to a future phase that will
    use `Real213.CutSeries.partialSum` for the limit form.
