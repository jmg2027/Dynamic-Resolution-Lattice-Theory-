# Real213 — Module Index

213-native real-number type via Dedekind cut.  185 files: 13 top-level + 172 in
20 sub-clusters.

Path = namespace: each module's namespace carries its cluster segment (e.g.
`…Real213.Phi.PhiCut`); cross-cluster references resolve via a cluster-parent
`open` (e.g. `open …Real213.Mobius`).

## Sub-clusters

Foundation / cut algebra:

| Dir | Files | Topic |
|---|---|---|
| `Core/` | 12 | type + Equiv + ValidCut + Dyadic + Functions + Poset |
| `Sum/` | 16 | cutSum + signedSum family + assoc (B3, Int) |
| `Mul/` | 18 | cutMul/Inv/Pow/Poly + ConstCutScale + CutBinary/Double/Distance |
| `Lattice/` | 5 | cutMax/Min/Mid + LatticeEq + ScaleLattice |
| `Bisection/` | 3 | bisection + continuity (CutBisection{,Algo}, CutContinuity) |
| `Calculus/` | 3 | cut integration (CutIntegral{,Linearity}) + DiffCutModulus |
| `ExpLog/` | 28 | CutExp/Log series + ODE + Geom* + EulerCut (e) / PiCut (π) + Lambert |

Specific reals / dynamics:

| Dir | Files | Topic |
|---|---|---|
| `Phi/` | 14 | golden ratio φ as cut, Fibonacci, Zeckendorf, Pell, Pentagon |
| `Markov/` | 9 | Markov spectrum/triple/uniqueness + Cassini/SternBrocot/Continuant bridges |
| `Mobius/` | 10 | Möbius transforms on cuts, Stern–Brocot, setoid, Pell invariant |
| `Minkowski/` | 7 | Minkowski `?`, modular symbols, period integrals/polynomials |
| `ModularGeometry/` | 12 | elliptic/hyperbolic/parabolic traces, geodesic lens, holonomy, finite-order spectrum, Lagrange extremes |
| `Mat2/` | 3 | 2×2 matrix algebra (assoc, Cayley–Hamilton, trace recurrence) |
| `ProbeTwist/` | 3 | probe-twist dynamics, conic, fixed point |
| `Spiral/` | 4 | spiral coordinate/layer/rotation invariant + scaling orbit |

Approximation / completeness:

| Dir | Files | Topic |
|---|---|---|
| `ValidCut/` | 7 | rational instances (½, ⅓, ⅕, ℤ, ℕ, ℕ-mul) + framework |
| `CrossDet/` | 4 | cross-determinant overtake / const-denom / eq-denom / trace-field |
| `ContinuedFraction/` | 3 | continuant + continued-fraction floor / modulus |
| `Modulus/` | 5 | convergence-rate moduli (bracket, Liouville, rate, stratification, composition) |
| `Completability/` | 6 | completability grade, intensional/refined/tower completion, geometric threshold |

## Module notes (by topic)

`Real213.lean` — umbrella aggregator.

The thematic notes below correspond to the directories in the table above
(13 modules stay at the top level: `AbCutSeq`, `ChainToCut`, `CubeRootTwoCut`,
`FloorReferenceForm`, `HolonomicReal`, `NuEscape`,
`ObjectIsReadingScaleInvariant`, `OdometerSternBrocotUnit`, `OracleContinuity`,
`PresentationDependence`, `ReciprocalSeries`, `Zeta3Apery`, `Zeta3Cut`).

**Named-constant cuts via `AbCutSeq`**:
  - `AbCutSeq.lean` — ★ every monotone-bounded ab-sequence is a `Real213` cut
    (the shared carrier: valid/ratio/nesting/eventual-const/completion/
    `limit_brackets`).  Instances: `ExpLog/EulerCut` (e), `ExpLog/PiCut` (π),
    `PhiAbCut` (φ).
  - `PhiAbCut.lean` — φ as an `AbCutSeq`; the algebraic/transcendental split as a
    theorem (φ completes with closed-form modulus `N=2k`, e/π take it as a
    hypothesis — algebraicity *is* the closed-form modulus).
  - `Zeta3Cut.lean` — ★ **ζ(3) as a constructed fold + the reduced-route engine**: the Apéry recurrence
    (the `DepthAperyCubic` degree-3 coefficients) made exact over ℕ by a
    growth-invariant engine (`aperyOrbit_exact`), the Casoratian in closed form
    (`zeta3_cross_det`: cross-det `= aperyCasDet m = 6·(m!)⁶`), the convergents
    an `AbCutSeq` with bracket `601/500 < ζ(3) ≤ 1203/1000`
    (upper bounds are themselves orbits — `aperyOrbit_linear`), completion to a
    `ValidCut` limit.  Honest stratum: the factorial-cleared presentation is
    *proved* rate-free (`zeta3_presentation_overtakes`, `RateStratification`
    overtake at layer 9) — the constructed-modulus upgrade is the reduced
    presentation, whose **engine end is done**: `aperyOrbit_geom` (orbit grows
    `≥ 28·(m+1)³` per layer from layer 7; `28 > 27 = 3³` = the Hanson race
    margin) + `zeta3_reduced_conditional` (I1 integrality + I2 reduced
    smallness ⟹ total modulus `N = k+n₀+2` for the original cut).  The two
    classical Apéry inputs (I1, I2) are the recorded frontier.
  - `CubeRootTwoCut.lean` — ★ **∛2: the degree-3 form-margin modulus**.
    Side-decision reduces to the all-additive `ε·k³ < d³` (the form margin
    `|m³−2k³| ≥ 1` = `Nat` strictness `+1`); dyadic bisection presentation ⟹
    total modulus `N(m,k) = 3k+5` (`cbrtCauchySeq`) — the first degree-3 member
    of the unconditional class, by the *form*, not the rate race.  The fold
    lands on the frozen closed-form cut `decide (2k³ ≤ m³)`
    (`cbrt_limit_eq_form`); bracket `5/4 < ∛2 ≤ 13/10`.  Degree-2 shadow:
    `FibCassiniNat.qb_lt_pk` (`4k² < b²`).
  - `ModulusComposition.lean` — ★ **schedules with irrational degree**:
    `powSched c B k = ⌈k^{p/2^k}⌉` with the exponent read off a cut (`dyUp` +
    exact `rootCeil`); calibrated to `k^s` at integer exponents
    (`powSched_rat`); instances at degree ∛2 (`cbrtPow_at_two = 3`) and degree
    e (`ePow_at_two = 7`, the kernel running `eulerCauchySeq.N` inside the
    schedule); `reschedule` + `eSelfScheduled` (e's modulus written through
    e's own modulus, limit-preserving) — receipts taking receipts as
    arguments.
  - `MobiusProbeTwist.lean` — the cut-probe lattice `(m,k)` is twisted by the
    Möbius `P = [[2,1],[1,1]]` (`Pstep (m,k) = (2m+k, m+k)`); P preserves rational
    order (det `= NS−NT = 1`), so the twist sends cuts to cuts
    (`cutThroughP_ratio`).  The two probe axes are braided by the `(NS,NT)=(3,2)`
    matrix.
  - `PhiProbeFixed.lean` — ★ **φ is the fixed cut of the probe-twist**:
    `cutThroughP phiCut = phiCut` (∀, PURE).  The cut-level shadow of "φ is the
    eigenvector of P".  Both sides reduce to the subtraction-free master invariant
    `masterCut m k = decide(k ≤ 2m ∧ mk+k² ≤ m²)` (the φ-norm `m² ≥ mk+k²`).
  - `ProbeTwistFixedPoint.lean` — the dichotomy: φ's cut is twist-fixed, a
    transcendental's is not (`e_not_fixed`: `cutThroughP (eulerCut 4) 3 1 ≠
    eulerCut 4 3 1`, witnessed by the probe `3/1 ↦ 7/4`).  φ is the twist's
    eigen-direction; e/π are moved by the two-axis braid.
  - `ProbeTwistDynamics.lean` — ★ *how* a non-φ cut wobbles: `twist_undoes_step`
    proves `cutThroughP (constCut (2p+q)(p+q)) = constCut p q`, i.e. the probe-twist
    runs the Pell recurrence **backwards** on the value (`f⁻¹`, expanding away from
    φ), the exact inverse of advancing the convergents (`f`, contracting toward φ).
    φ is the lone common fixed point `f(φ)=f⁻¹(φ)=φ`.
  - `ProbeTwistConic.lean` — ★ the *shape* the wobble traces: `Q_preserved` proves
    `Pstep` conserves the φ-norm `Q(m,k) = m²−mk−k²` (sign-free Nat form), so each
    orbit stays on its hyperbola `Q = N` (φ-convergents on `Q=−1`, the `(2,1)`-orbit
    on `Q=+1`, e's `(65,24)` on `Q=2089`).  `N` is the conserved orbit-label;
    φ the common asymptote (discriminant `5 = NS+NT`).
  - `SpiralRotationInvariant.lean` — ★ the rotation invariant conserved at **every** turn:
    `Q_iterate_preserved` — `Q(Pseq (m,k) n) = Q(m,k)` for all `n` (induct + `Q_preserved`,
    via the pure additive `add_cancel_chain`).  The golden form is the scale-invariant of
    the self-similar `P`-shift — the same form preserved identically at every iteration.

**Modulus + tower-native completeness + stratification** (narrative
`theory/math/analysis/{holonomic_modulus, tower_native_completeness}.md`):
  - `RateModulus.lean` — ★ the "rate-carrying ⟹ total modulus" generator, graded by
    probe schedule.  A monotone convergent cut `a_i/d_i` with a non-increasing
    scheduled margin `e_i + 1/(ρ_i·d_i)` (`HtelS`, the graded rate certificate)
    completes past any layer admitting the probe (`rateS_total_modulus`); the
    identity schedule is `Htel` / `rate_total_modulus` (`N=k+2`), the degree-`s`
    root schedule (`Meta.Nat.RootFloor`) is `graded_total_modulus` (`N=k^s+1`) —
    an `r^{s−1}` factor of overtake forgiven at the admission layer `i=r^s`, paid
    as modulus degree.  `Htel_of_crossdet` reduces the certificate to a *smallness
    law* on the cross-determinant `W_i = a_{i+1}d_i − a_i d_{i+1}` against the
    denominator's discrete growth — the bridge where the divergence ladder (`W`)
    meets the modulus generator.
  - `HolonomicReal.lean` — the `Holonomic`/`HolonomicReal` bundle (recurrence + Cauchy
    cut-sequence + valid limit); φ and e instances with constructed modulus.
  - `RateStratification.lean` — ★ the smallness law as a layer-by-layer **W-vs-d
    comparison**, graded by schedule.  `DominatesS W d ρ i` (the ladder's
    `Dominates_s`; `Dominates` the identity instance); `htelS_iff_dominatesS`
    upgrades `Htel_of_crossdet` from implication to *characterization* (`HtelS` ⟺
    scheduled domination at every layer); `dominated_free_modulus` /
    `dominatedS_graded_modulus` (`N=k+2` / `N=k^s+1`); `overtakeS_breaks_layer`
    (the boundary); the unimodular det-1 floor (`W ≡ 1`, `T=[[2,1],[1,1]]`) is
    dominated against `d_i=(i+1)(i+2)` everywhere (`floor_dominates_all`) — the
    trivially-free bottom (`tower_stratification`); and the grading is **strict**:
    `sepDen` (`d_{i+1}=(⌊√i⌋+2)·d_i`, `W=d`) is root-2-dominated everywhere yet
    breaks `Dominates` at layer 4 (`graded_stratification`), and the witness is
    an actual presentation — `sepNum/sepDen` completes through the degree-2
    schedule with constructed modulus `N=k²+1` (`sep_graded_modulus`).  The
    **schedule comparison law**: `dominatesS_schedule_mono` (slower schedule
    inherits domination under the cross-multiplied **gap law**
    `1/ρ' − 1/ρ` non-increasing) + `schedule_comparison_needs_gap` (the gap
    law is indispensable — pointwise the ladder is not a chain).
  - `RateHierarchy.lean` — ★ the lone degree-2 witness promoted to a **uniform
    family** `sepDenS s` (`d_{i+1}=(⌊i^{1/s}⌋+2)·d_i`, `W=d`; `sepDenS 2 = sepDen`).
    `sepDenS_dominatesS_all` (degree-`s` rescue at every layer) +
    `sepDenS_breaks` (degree-`t` schedule fails at the perfect power layer
    `(t+3)^t`, via the cross-degree gap `Meta.Nat.PowBernoulli.pow_pred_lt`) give
    `strict_modulus_hierarchy`: every consecutive rung `(t,t+1)` is separated, so
    the modulus-degree ladder is **infinite and strict**.  `sepS_graded_modulus`
    occupies each rung with an actual real (`sepNumS s / sepDenS s`, modulus
    `N=k^s+1`) — degree exactly `t+1` for every `t`.  §6 the dual:
    `fastDen_dominates` — *any* cross-determinant `W` is degree-1 with the
    fast denominator `d_{i+1}=i·W_i+d_i` (the bottom rung is generously
    inhabited; the race is `W`-vs-`d` growth, witnessed by e's `W=i!` at `N=k+2`).
  - `RateComparison.lean` — ★ the **two-real joint cut** (open frontier closed):
    deciding `a_i/d_i ⋚ b_j/e_j` between two rate-carrying reals via the
    two-convergent cross-determinant `a_i·e_j − b_j·d_i` (the single-probe
    Farey/SL₂ `det` with `m/k` promoted to a second convergent).  `two_cut_decided`
    (a separating rational forces the joint sign) + `two_real_separation_modulus`
    (given an apartness witness `m/k`, the comparison is settled for all
    `i,j ≥ k+2` — the two single moduli compose by `max`); `rcut2_const_true` the
    decided-Bool form.
  - `DegreeCriterion.lean` — ★ **what fixes the degree**: the two-sided
    `W`-vs-`d`-increment criterion.  `dominatesS_of_scheduled_increment`
    (sufficient: `ρ_i·W_i + d_i ≤ d_{i+1}`) and `scheduled_le_of_dominatesS`
    (necessary: domination ⟹ `ρ_i·W_i ≤ d_{i+1}`) bracket domination, gap exactly
    `d_i`; `degree_le_of_increment` / `not_dominatesS_of_overtake` the `rootFloor s`
    readings.  `rootFloor_antitone_degree` (bigger `s` = slower probe) ⟹
    `increment_criterion_mono` (the criterion is upward-closed in degree, so the
    ceiling is well-defined).  The degree-1 boundary `i·W_i + d_i = d_{i+1}` is
    saturated by `RateHierarchy.fastDen` and e (`W=i!`).
  - `RateArithmetic.lean` — ★ the cross-determinant under **sum/product**, and why
    degree is not additive.  `sum_cross_det` (`W^{x+y}=W^x·e_i e_{i+1}+W^y·d_i d_{i+1}`)
    and `prod_cross_det` (`W^{xy}=a_i d_{i+1}W^y+b_i e_{i+1}W^x+W^x W^y`) factor the
    arithmetic cross-determinants through the summands'.  `sum_naive_not_dominatesS`:
    the sum carries the *other* denominator quadratically, so naive convergent
    addition breaks the rate at *any* degree when denominators are mismatched
    (`d_{i+1}<e_i`) — degree is a property of the pointing, not of `x+y`; closure
    holds only with a good presentation.  The clean matched closure:
    `matched_sum_cross_det` (shared denominator ⟹ cross-determinants *add*,
    `W^x+W^y`, no inflation) + `matched_sum_dominated` (sum degree ≤ s iff the
    probed cross-determinants *jointly* fit the shared increment; "each at degree s"
    is a factor of 2 short — degree is set by `W^x+W^y`, not the max).
  - `PointingLimit.lean` — ★ the conceived limit is a **pointing**, not a value.
    `conv_strict_increase` (convergent values strictly advance across every gap —
    the limit is reached by no term) + `limit_unreached_but_decided` (reached by no
    value, yet every cut decided past a finite layer): the infinity enters
    computation only as the discrete modulus, never as a value.  Narrative:
    `theory/essays/foundations/imagining_infinity.md`.
  - `BestApproximation.lean` — ★ the cross-determinant **is** the Diophantine
    approximation deficiency.  `denominator_lower_bound` (a rational strictly between
    consecutive convergents has `k·W_i ≥ d_i + d_{i+1}` — interposing costs denominator
    `≥ (d_i+d_{i+1})/W_i`) + `unimodular_best_approximation` (`W=1` ⟹ `k ≥ d_i+d_{i+1}`,
    the convergents are optimal — constructive core of `μ ≥ 2`).  The residue's shape
    `W` measures distance from optimal approximation — the `μ`-content, no `limsup`.
  - `BracketModulus.lean` — ★ the conversion-law engine for **two-sided bracket
    presentations**: strictly increasing lower fold + non-increasing upper
    companion + per-layer sandwich; one hypothesis — the **exclusion depth** `B`
    (probe still `Inside` the layer-`n` bracket ⟹ `n ≤ B k`) — yields the total
    modulus `N(m,k) = B k + 2` (`bracket_total_modulus`).  Where an effective
    irrationality measure enters as `B k = C·k^s` (ladder rung 2); instance:
    `ExpLog/PiMeasureModulus` (Wallis-π).
  - `CrossDetOvertake.lean` — ★ completability boundary: `CrossDetSmall`, below ⟹ free,
    the double-exponential overtake break.  (Companion to `RateStratification`: the same
    W-vs-d boundary, presented as a `CrossDetSmall` predicate + double-exp witness.)
  - `LiouvilleModulus.lean` — ★ the Liouville constant's cross-determinant equals its
    denominator (`W=c^{k!}`), so it carries a free modulus — tame on this axis.
  - `CrossDetEqDenom.lean` — ★ the general `W=d` theorem behind both e and Liouville
    (`crossdet_eq_denom_total_modulus`); both reprove as one-liners.
  - `ReciprocalSeries.lean` — ★ the `W=d` line as a ratio-parametrized reference family:
    `Σ 1/d` reciprocal series from a ratio `g` (`recip_total_modulus`, free iff `g_i≳i`);
    e = linear-ratio point (`den (·+1) = factorial`).
  - `CrossDetConstDenom.lean` — ★ the `W=const` rung (`crossdet_const_total_modulus`) +
    φ (Fibonacci convergents `fib(2i+2)/fib(2i+1)`) as its named instance, through the
    same bridge as e/Liouville.
  - `GeometricThreshold.lean` — ★ the exact growth-rate boundary: geometric `W=r^i`
    over `d=q^i` is free **iff** `r < q` (`geom_boundary_iff`).
  - `PresentationDependence.lean` — ★ `CrossDetSmall` reads the representation, not the
    real: `rcut` is rescaling-invariant (`rcut_rescale`) while the smallness condition
    is not (e's `×2` representation breaks it — same real).
  - `IntensionalCompletability.lean` — ★ the intensional reduction: the bridge
    `CrossDetSmall` is antitone under rescaling (`crossDetSmall_rescale_antitone` —
    rescaling up only loses it, so the gcd-reduced presentation is canonical), while the
    *completion* is presentation-invariant (`modulus_rescale_invariant`).  The test is
    presentation-relative; the truth (the cut's completion) is not
    (`completability_is_intensional`).
  - `ScalingOrbit.lean` — ★ the rescaling orbit `(c·a, c·d)` of a presentation: a monoid
    action (`scaleBy_one`/`scaleBy_comp`) inside one cut (`scaleBy_preserves_cut`), with
    `CrossDetSmall` antitone along it (`orbit_free_implies_base_free`) and a unique
    `Reduced` base (`reduced_scaling_trivial`) — the canonical point to read the cut's
    rung (`scaling_orbit_structure`).
  - `FloorReferenceForm.lean` — ★ the det-one floor's reference form is **indefinite**:
    the golden `Q = m²−mk−k²` (`ProbeTwistConic.Q_preserved`, the P-orbit invariant) takes
    both signs (`golden_indefinite`, `Q(2,1)=+1`, `Q(1,1)=−1`) → unbounded hyperbolic
    orbits → convergent line → the completing bottom rung (`floor_reference_is_indefinite`).
    The completability-side (disc+5, line) complement of `EisensteinSignature` (disc−3,
    curve).
  - `TowerNativeCompleteness.lean` — ★ `tower_native_completeness_program`, the five
    pieces (boundary, Liouville, closure, generator, residue) bundled.

**SL(2,ℤ) trace trichotomy + the cross-determinant number field**:
  - `ModularElliptic.lean` — the elliptic generators `S` (order 4, fixes `i`) and `U`
    (order 6, fixes `ω`) of `SL(2,ℤ)`; orders `{4,6}` = the Gaussian/Eisenstein
    unit-group orders, `−I` the central Cassini `2`.
  - `HyperbolicBoost.lean` / `ParabolicTranslation.lean` — the trichotomy as products of
    two reflections, with `tr²−4` the dial: golden boost `G` (disc `+5`, hyperbolic),
    translation `T` (disc `0`, parabolic), rotation `S` (disc `−4`, elliptic)
    (`sl2_trichotomy_as_two_reflections`).
  - `EllipticTracePeriodic.lean` / `UTracePeriodic.lean` — the elliptic traces are
    periodic (period 4 for `S`, period 6 for `U`), bounded `|tr| ≤ 2`, against the
    hyperbolic unbounded growth (`elliptic_orders_four_and_six`).
  - `CrossDetTraceField.lean` — ★★★★ the capstone: the cross-determinant's **number
    field is the modular trace field**.  The fixed-point form `fixForm M = (c, d−a, −b)`
    of the Möbius map has discriminant `tr²−4` identically (`fixForm_disc_eq_traceDisc`,
    a `ring_intZ` identity ∀ `M`), and on the three faces recovers the signature
    reference forms on the nose — `fixForm G` = golden (disc `+5`, line),
    `fixForm U` = cyclotomic `x²+x+1` (root `ω`, disc `−3`, curve), `fixForm T` = the
    `∞`-cusp form (disc `0`).  The sign of `D = tr²−4` is simultaneously the
    line/cusp/curve and hyperbolic/parabolic/elliptic dial
    (`crossdet_number_field_is_trace_field`, `disc_sign_is_line_cusp_curve`).

**Markov spectrum + modular-geodesic** (narrative
`theory/math/analysis/markov_uniqueness.md` +
`theory/essays/p_orbit/the_modular_geodesic_lens.md`):
  - `MarkovTree.lean` / `MarkovUniqueness.lean` / `MarkovInjectivity.lean` —
    the Markov-number tree, the uniqueness statement, and the injectivity
    reading (`markovNum` injective ⟺ `MarkovMaxUnique`).
  - `SternBrocotMarkov.lean` — ★ the Stern-Brocot ⟷ Markov bridge: size
    reading strictly monotone under descent (§30), slope determines size
    (§32), the forward + reverse bridges closing the iff
    (`markovMaxUnique_iff_markovNum_injective`, §33–§34), and the orbit-
    realizability kernel `H` (`OrbitRealizabilityH`).
  - `Continuant.lean` — Euler continuants `K[a₁..aₙ]` + monotonicity (the
    Aigner core tool for the continuant/Markov program).
  - `ZeckendorfCarry.lean` — the golden (Fibonacci-base) odometer carry
    `011 → 100` = the Fibonacci recurrence, value-preserving (`golden_adic_carry`);
    admissibility = Cassini.  The residue's own variable base (Ostrowski(φ)),
    companion to the binary `Theory/Raw/Odometer`.
  - `OdometerSternBrocotUnit.lean` — the odometer (dyadic `Theory/Raw/Odometer`)
    and the Stern-Brocot mediant tree (`SternBrocotMarkov.mInterval`) share the
    `List Bool` path index + the unimodular unit (`det genL = NS−NT = 1`); the
    shared residue unit across the two `List Bool`-indexed descents.
  - `ModularGeodesicLens.lean` — ★ the geodesic engine as a Raw-Lens:
    `mediantLens` + `mediantLens_view_reachable` (mediant-Lens view ⊆
    `SternBrocotReachable`, ∅-axiom) — the residue read at `ℍ/PSL(2,ℤ)`.

**`cutSumN` associativity closures + named-`b` cut bundles**:
  - `ThirdValidCut.lean` / `FifthValidCut.lean` / `HalfValidCut.lean` —
    bundled `b = 3 / 5 / 2` cuts, explicit `ValidCutN` instances closing
    `cutSumN` associativity at their denominators.
  - `CutSumAssocB3.lean` — `cutSum_assoc` at `b ≥ 3`, the
    precision-artifact honest closure.
  - `PellFibCutBridge.lean` — the Pell convergents ARE the Fibonacci
    convergents (∀n, PURE).
  - `OracleContinuity.lean` — oracle-based continuity, eliminating the
    ε-δ residue from `Real213`.

## Architecture notes

- Real = (sequence + modulus) pair — type-level form of Cauchy completeness.
- Cut = `Nat → Nat → Bool` (m, k ↦ "value ≤ m/k").
- Real213 marathon: ~90% PURE — most CutSum/CutMul/Lattice
  paths propext-free via pointwise eq + ChainToCut bridge.

PURE 진행: see STRICT_ZERO_AXIOM.md.
