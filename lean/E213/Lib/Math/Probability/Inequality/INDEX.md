# `Probability/Inequality/` — concentration inequalities

213-native concentration inequalities: Markov, Chebyshev, Hoeffding,
Chernoff (graded), general concentration.

## Files (6)

  - `Markov.lean`           — Markov inequality
  - `Chebyshev.lean`        — Chebyshev inequality
  - `Hoeffding.lean`        — Hoeffding inequality (base form)
  - `HoeffdingClosed.lean`  — Hoeffding closed-form variant
  - `ChernoffGrade.lean`    — Chernoff bound (graded)
  - `Concentration.lean`    — general concentration combinator

## Where to add new files

  - New inequality            → `<Name>.lean` (Bernstein, Azuma, etc.)
  - Variant of existing       → `<Name>Closed.lean` / `<Name>Grade.lean`
  - Concentration combinator  → `Concentration*`

## Companion sub-clusters (in `Probability/`)

  - `Foundation/`   — expectation, variance, independence (consumed)
  - `Distribution/` — specific distributions
  - `Limit/`        — LLN / CLT (consumes these inequalities)
  - `Bridge/`       — bridges to other Math clusters
