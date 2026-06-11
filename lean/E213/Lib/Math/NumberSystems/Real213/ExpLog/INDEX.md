# `Real213/ExpLog/` — exp / log / geometric series

Exponential and logarithm on Real213 cuts via power-series + ODE.
Plus geometric series identity and Cauchy convergence proofs.

## Files (28)

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
  - `LambertWeld.lean`          — the weld core: Lambert three-term ladder
                                  (`weld_ladder`), pairing functional `PF` +
                                  convergent lists `AP/BP` (`weld_pair_cosh/sinh`),
                                  descending evaluation `dev` + `cf_bridge` (CF
                                  convergents = `dev` of the lists), `row_det`
                                  collapse, and the Chebyshev engine
                                  (`weight_dom`, `cross_le`: minor condition ⟹
                                  cross order transfer).
  - `LambertMinor.lean`         — the minor-sign system: coefficient functions
                                  `apF/bpF` (totalized), prefix support, the
                                  closed 4-family induction `minorSys` (adjacent
                                  minors + 3 cross-level families; two-apart `E`
                                  derived by `ratio_chain` with zero-pivot
                                  fallback), and the all-gap form `minor_all`.
                                  Continuant total positivity, the input
                                  `cross_le` consumes.
  - `LambertOrder.lean`         — **the order transfer**: `nth`-transport of the
                                  sign system onto the weld lists; `series_le_odd`
                                  (the series below EVERY odd convergent — the
                                  full (A′) family, `cross_le` twice + det-one
                                  floor pivot); `cf_limit_false_of_series_false`
                                  (W1, choice layer `k·s_J+k+2`); the lower
                                  transfer reduced to its matched base
                                  (`lower_step`/`LowerBase`); the weld pipeline
                                  `weld_limit_agreement` + `cothSeriesCauchySepOfBase`
                                  (consumes `LowerBase`, proven in `LambertBridge`).
  - `LambertMasterId.lean`      — **the master identity** (Padé-cancellation
                                  core): `Asum(2k+1,N) + cfpos(2k+1,N) =
                                  Bsum(2k+1,N)` (+ even twin), all-ℕ via the
                                  weight-threading accumulators `Bacc/Aacc`;
                                  engine `cfpos_moved` (the `binom_absorption`
                                  analog); `master_diagonal` = the `(4i+2)!!`
                                  flip value `LowerBase` consumes.
  - `LambertPoly.lean`          — the graded connection layer: `evc`
                                  (constant-first evaluation, length-condition-
                                  free) + `lmulC` convolution + `dev`-bridge;
                                  `evc_dom_joint` (the Abel transfer: suffix
                                  dominance ⟹ all-`q` dominance);
                                  `lowerbase_of_suffdom` + end-to-end `i = 1`
                                  (`lowerbase_one`).  General `i`: `LambertBridge`.
  - `LambertBridge.lean`        — **the weld closes**: `lowerBase` (the base
                                  inequality, every `q ≥ 1`, every `i`) via the
                                  convolution–master bridge — reversed convergent
                                  stacks (`rev_trunc`), accumulator snoc + weight
                                  `wprod`, the bridges (`bridgeA/B`: stack
                                  coefficients complete the accumulators), mirrors
                                  past the stack, saturation, the division-free
                                  budget (`budgetGen`), diagonal flip `cfpos n n =
                                  (4i+2)!!`, suffix descent (`inv_descent`) ⟹
                                  `SuffDom` ⟹ `lowerBase`; `cothSeriesCauchySep` +
                                  `weld_closed` — series ≡ CF for `coth(1/q)`,
                                  **no hypotheses**.  77 PURE.
  - `ExpMoebius.lean`           — **`exp(2/q)` completes unconditionally**: the
                                  cut-Möbius step — odd Lambert convergents under
                                  `z ↦ (z+1)/(z−1)` climb with cross-det
                                  `2·a_{2L+3}` (doubled det-one floor); `dN =
                                  p − q` rides the same recurrence; total modulus
                                  `k+2`, no hypotheses (`expTwoOverQCFCauchySeq`).
                                  `e² ∈ (22/3, 37/5]`.
  - `CothSeriesCut.lean`        — weld 3b: the coth series as a fold
                                  (`cothSeriesAb`, truncated ratio
                                  `(2J+1)q·coshNum/sinhNum` climbs via the exact
                                  `q²`-cancelling cross identity); the CF and
                                  series pointings agree on the `(5/4, 3/2]`
                                  probes (`two_pointings_agree`); the ∀-probe
                                  transfer is closed (`LambertBridge.weld_closed`).
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
