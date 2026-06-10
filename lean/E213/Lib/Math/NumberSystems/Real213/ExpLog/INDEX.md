# `Real213/ExpLog/` — exp / log / geometric series

Exponential and logarithm on Real213 cuts via power-series + ODE.
Plus geometric series identity and Cauchy convergence proofs.

## Files (18)

### Exp
  - `CutExpSeries.lean`         — `exp` Taylor series
  - `CutExpODE.lean`            — `exp` ODE characterisation
  - `CutExpModulus.lean`        — `exp` Taylor convergence modulus (ratio-test
                                  core: geometric majorant `Mⁿ/n!`, term decay
                                  `≤ term(2M)·2^{−j}`, terms antitone).  Marathon T1.
  - `CutExpConvergents.lean`    — exp(m) rational convergents + cross-determinant
                                  (algebraic route; generalizes e to all integer
                                  args; clean RateModulus rate is m=1-special).  T1.
  - `CutTrigModulus.lean`       — `sin`/`cos` Taylor convergence modulus by
                                  comparison to `exp` (odd/even index sampling:
                                  geometric decay + antitone).  Marathon T2.
  - `CutFactorial.lean`         — factorial coefficient
  - `EulerCut.lean`             — e (= exp 1, Σ1/k!) at the `ValidCut` level: an
                                  `Real213/AbCutSeq` instance + e's localization
                                  in (8/3, 3).  Generic cut interface inherited;
                                  this file adds only the bracket.
  - `PiCut.lean`                — π/2 (Wallis product) and π: an `AbCutSeq`
                                  instance, π/2 ∈ (7/5, 2), π ∈ (14/5, 4).
  - `PiMeasureModulus.lean`     — π/2 and π **conditionally degree-`s`**: the
                                  decreasing upper companion `U_n = W_n·(2n+2)/(2n+1)`
                                  makes a per-layer shrinking bracket;
                                  `PiHalfMeasure C s` (effective measure, one ℕ
                                  inequality) ⟹ total modulus `N = C·k^s + 2`
                                  via `Real213/BracketModulus` (ladder rung 2);
                                  and the unconditional negative: `W_n = a_n·d_n`
                                  (`wallis_cross_det`) overtakes **every**
                                  schedule — the Wallis pointing's rung is ∞
                                  (`wallis_no_graded_certificate`).

Both are thin instances of the shared `Real213/AbCutSeq.lean` (every
monotone-bounded ab-sequence is a `Real213` cut): valid/ratio/nesting/eventual-
constancy/completion/`limit_brackets` live once there.  The transcendental's
completion modulus is a *hypothesis* (no LEM-free total cut), unlike algebraic φ —
refined for π by `PiMeasureModulus` to a single effective-measure hypothesis with
a constructed `C·k^s + 2` modulus.

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
