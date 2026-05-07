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

## Synthesis

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Capstone.lean` | Phase EA + EB + EC + ED synthesis bundles | 4 | ∅-axiom |
| `Probability.lean` | umbrella | — | — |

**Total**: 95 atomic facts, all ∅-axiom verified.

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

## Next phases (per blueprint)

  * **Phase EE** — CLT + Gaussian peak.
  * **Phase EF** — Final capstone (18+ fact bundle).

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
