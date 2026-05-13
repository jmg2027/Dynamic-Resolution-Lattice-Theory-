# `Real213/ExpLog/` — exp / log / geometric series

Exponential and logarithm on Real213 cuts via power-series + ODE.
Plus geometric series identity and Cauchy convergence proofs.

## Files (11)

### Exp
  - `CutExpSeries.lean`         — `exp` Taylor series
  - `CutExpODE.lean`            — `exp` ODE characterisation
  - `CutFactorial.lean`         — factorial coefficient

### Log
  - `CutLogSeries.lean`         — `log` Taylor series
  - `CutLogODE.lean`            — `log` ODE characterisation
  - `CutLogCapstone.lean`       — log capstone result
  - `CutLogExpInverse.lean`     — exp / log inverse property
  - `CutLogCauchyConvCapstone.lean` — Cauchy convergence capstone

### Geometric series
  - `GeomSeriesIdentity.lean`   — Σ x^k = 1/(1-x) identity
  - `GeomSeriesCauchy.lean`     — Cauchy form
  - `GeomCutInvBridge.lean`     — geometric ↔ cutInv bridge

## Where to add new files

  - New exp / log lemma     → `CutExp<...>` / `CutLog<...>`
  - Series identity         → `GeomSeries<name>`
  - Convergence proof       → `<...>Cauchy*` / `<...>Capstone`
