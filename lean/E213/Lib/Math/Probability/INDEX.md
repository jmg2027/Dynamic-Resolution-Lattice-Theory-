# Probability 213 — Module Index (sub-organized 2026-05-13)

Atomic dyadic probability — no σ-algebra, no σ-additivity.
25 files in 5 sub-clusters.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `Foundation/` | 7 | Cut/Bernoulli/Expectation/Variance/Independence/SampleMean/Capstone |
| `Distribution/` | 5 | Binomial/Gaussian/UniformOnUnit/Beta{Density,Normalized} |
| `Inequality/` | 6 | Markov/Chebyshev/Hoeffding{,Closed}/Concentration/ChernoffGrade |
| `Limit/` | 4 | LLN/LLNCauchy/CLT{Limit,Generic} |
| `Bridge/` | 3 | RiemannBridge/CauchyModulus/Bayesian |

## Top-level

`Probability.lean` — umbrella aggregator.

## 213-native paradigm

- **Probability = atomic rational mass**: `num/den` with `0 < den`,
  `num ≤ den`.  No σ-algebra; no measure-theoretic completion.
- **bit = dyadic bisection**: Information theory anchor — cf.
  `Lib/Math/Probability/Information/Bit.lean`.
- All Capstones `#print axioms` empty (∅-axiom standard).

Blueprint: `blueprints/math/01_probability_213.md`.
