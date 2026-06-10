# `Real213/ExpLog/` — exp / log / geometric series

Exponential and logarithm on Real213 cuts via power-series + ODE.
Plus geometric series identity and Cauchy convergence proofs.

## Files (19)

### Exp
  - `CutExpSeries.lean`         — `exp` Taylor series
  - `CutExpODE.lean`            — `exp` ODE characterisation
  - `CutExpModulus.lean`        — `exp` Taylor convergence modulus (ratio-test
                                  core: geometric majorant `Mⁿ/n!`, term decay
                                  `≤ term(2M)·2^{−j}`, terms antitone).  Marathon T1.
  - `CutExpConvergents.lean`    — exp(m) rational convergents + cross-determinant
                                  (algebraic route; generalizes e to all integer
                                  args; clean RateModulus rate is m=1-special).  T1.
  - `ExpUnitModulus.lean`        — **`exp(1/q)` family completes unconditionally**:
                                  convergents `a_n/(qⁿ·n!)`, cross-det `= dₙ`,
                                  `Htel` uniform in `q ≥ 1` ⟹ `expUnitCauchySeq`
                                  (total modulus `N(m,k)=k+2`); `√e` instance;
                                  `q = 1` ≡ euler.  exp(p/q), p ≥ 2: open (offset
                                  modulus or cut-power route).
  - `ExpRationalCut.lean`       — **`exp(p/q)` as a constructed fold** (`AbCutSeq`,
                                  every positive rational arg): convergent carrier +
                                  doubled-tail upper bracket (`upNum`, geometric
                                  halving past `2p ≤ (N+2)q`); `e² ∈ (7, 904/120]`.
                                  Free modulus open (`exp_pq_no_htel` boundary).
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

Both are thin instances of the shared `Real213/AbCutSeq.lean` (every
monotone-bounded ab-sequence is a `Real213` cut): valid/ratio/nesting/eventual-
constancy/completion/`limit_brackets` live once there.  The transcendental's
completion modulus is a *hypothesis* (no LEM-free total cut), unlike algebraic φ.

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
