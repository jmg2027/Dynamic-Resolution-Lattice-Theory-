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

## Synthesis

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Capstone.lean` | Phase EA + EB synthesis bundles | 2 | ∅-axiom |
| `Probability.lean` | umbrella | — | — |

**Total**: 62 atomic facts, all ∅-axiom verified.

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

  * **Phase EC** — Law of Large Numbers.
  * **Phase ED** — Bayesian framework.
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
