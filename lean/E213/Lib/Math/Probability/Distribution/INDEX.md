# `Probability/Distribution/` — specific probability distributions

213-native specific distributions: Binomial, Gaussian, Beta,
uniform-on-unit.

## Files (5)

  - `Binomial.lean`        — Binomial(n, p) distribution
  - `Gaussian.lean`        — Gaussian / normal distribution
  - `BetaDensity.lean`     — Beta-density carrier
  - `BetaNormalized.lean`  — Beta normalized form
  - `UniformOnUnit.lean`   — uniform on [0, 1]

## Where to add new files

  - New distribution     → `<Distribution>.lean`
  - Density / normalized → `<Dist>Density.lean` /
                            `<Dist>Normalized.lean`

## Companion sub-clusters (in `Probability/`)

  - `Foundation/`   — `Cut`, expectation, variance, independence
  - `Inequality/`   — concentration inequalities
  - `Limit/`        — LLN / CLT
  - `Bridge/`       — bridges to other Math clusters
