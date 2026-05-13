# `Probability/Foundation/` — probability foundation primitives

213-native probability foundation: distribution carrier (`Cut`),
expectation, variance, independence, sample mean, Bernoulli
distribution.

## Files (7)

  - `Cut.lean`           — distribution as a `Cut`
  - `Bernoulli.lean`     — Bernoulli distribution
  - `Expectation.lean`   — `𝔼[X]` operator
  - `Variance.lean`      — `Var[X]` operator
  - `Independence.lean`  — independence predicate
  - `SampleMean.lean`    — sample-mean construction
  - `Capstone.lean`      — Foundation capstone

## Where to add new files

  - New operator         → `<Operator>.lean`
  - New distribution     → `<Distribution>.lean`
  - Independence variant → `Independence*`

## Companion sub-clusters (in `Probability/`)

  - `Distribution/` — specific distributions
  - `Inequality/`   — probability inequalities (Markov, Chebyshev)
  - `Limit/`        — LLN / CLT
  - `Bridge/`       — bridges to other Math clusters
