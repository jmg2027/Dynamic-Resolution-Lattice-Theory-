# `Real213/ExpLog/` — exp / log / geometric series

Exponential and logarithm on Real213 cuts via power-series + ODE.
Plus geometric series identity and Cauchy convergence proofs.

## Files (12)

### Exp
  - `CutExpSeries.lean`         — `exp` Taylor series
  - `CutExpODE.lean`            — `exp` ODE characterisation
  - `CutFactorial.lean`         — factorial coefficient
  - `EulerCut.lean`             — e (= exp 1, Σ1/k!) at the `ValidCut` level:
                                  nested rational cuts, localized in (8/3, 3),
                                  irrational; per-threshold completion via
                                  `CauchyCompleteValid.limit_valid`.  The
                                  transcendental's modulus is a *hypothesis*
                                  (no LEM-free total cut), unlike algebraic φ.

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
