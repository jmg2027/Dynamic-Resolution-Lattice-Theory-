# The modulus-degree ladder — grading "completes" beyond the binary

**Question that opened this** (originator, 2026-06-10): what happens at modulus
degree 2, 3, … — `W ~ N(m,k)²`, `N(m1,k1)×N(m2,k2)`, or other shapes?

**Status**: the algebraic pillar is **closed** at degrees 2 and 3; the graded
rate generator (rung 1) is **closed** (`RateModulus.graded_total_modulus`,
`N = k^s + 1`); the **schedule-degree hierarchy is now closed as infinite and
strict** (`RateHierarchy.strict_modulus_hierarchy`: for every `t`, the family
`sepDenS (t+1)` separates rung `t` from `t+1`, via the cross-degree power gap
`PowBernoulli.pow_pred_lt`) — the lone degree-2 witness `sepDen` is now one rung
of a full ladder, each occupied by an actual real (`sepS_graded_modulus`); the
conditional measure-modulus schema (rung 2) is **closed** (`BracketModulus` +
`PiMeasureModulus`: π conditionally degree-`s`); the **two-real separation
modulus is now closed** (`RateComparison.two_real_separation_modulus`: given an
apartness witness `m/k`, the joint cut `a_i·e_j < b_j·d_i` — the two-convergent
cross-determinant — is settled for all `i,j ≥ k+2`; the two single moduli
compose by `max`).

## The conversion law (the frame)

A total cut modulus is always `N(m,k) = rate⁻¹(distance(m,k))` — a distance
lower bound composed with the inverse convergence rate.  The "degree" of the
modulus is the growth class of `N` in `k`, and it factors as
(degree of the distance certificate) / (rate exponent of the pointing).

**Precise W↔degree relationship (closed, `RateComparison`→`DegreeCriterion`)**:
degree-`s` domination is bracketed by `⌊i^{1/s}⌋·W_i + d_i ≤ d_{i+1}` (sufficient)
and `⌊i^{1/s}⌋·W_i ≤ d_{i+1}` (necessary) — the probed cross-determinant against
the denominator increment, gap exactly `d_i`.  The criterion is upward-closed in
`s` (`increment_criterion_mono`), so the degree is a well-defined ceiling: it is
the race between `W`-growth and `d`-growth, not `W`'s size.  Degree-1 boundary
`i·W_i + d_i = d_{i+1}` is saturated by `fastDen` and e (`W = i!`).

**Sum/product closure (clarified, `RateArithmetic`)**: the arithmetic
cross-determinants factor — `W^{x+y} = W^x·e_i e_{i+1} + W^y·d_i d_{i+1}`,
`W^{xy} = a_i d_{i+1}W^y + b_i e_{i+1}W^x + W^x W^y`.  The honest finding:
degree is **not additive** under naive convergent arithmetic — the sum carries the
other denominator quadratically, so a mismatched `e ≫ d` makes the naive sum
rate-free at every degree (`sum_naive_not_dominatesS`), even with both summands
degree 1.  Degree is a property of the *pointing*; closure of the completable
class needs a good presentation (e.g. scaling for `x+x`), not the common-denominator
one.  A clean degree-bounded closure on matched presentations remains **open**.

## Closed (the algebraic pillar)

- **Degree 2** — φ: the form `m²−mk−k²`, `|Q| ≥ 1`; closed-form cut
  (`PhiAsCut.masterCut`), and the squared comparison `4k² < b²` in
  `FibCassiniNat.qb_lt_pk` is the `ε·k² < d²` schema instance.
- **Degree 3** — ∛2 (`Real213/CubeRootTwoCut`, 31 PURE): side-decision reduces
  to the all-additive `ε_i·k³ < d_i³`; the `Nat` strictness `+1` *is* the form
  margin `|m³−2k³| ≥ 1`.  Dyadic bisection presentation ⟹ total modulus
  `N(m,k) = 3k+5`; the completed fold **equals** the frozen form cut
  (`cbrt_limit_eq_form`).  Key structural reading: the algebraic degree enters
  as the **probe exponent `k^s` in the schedule**, and the form makes the
  modulus presentation-robust — *any* presentation with a cube-slack rate
  completes.  The rate race (`W` vs `d`, `holonomic_modulus.md`) and its
  presentation-dependence (`Zeta3Cut.zeta3_presentation_overtakes`) are the
  transcendental-only regime.

## Rungs (status inline)

0. **The exact degree of an arbitrary irrational** (originator, second round).
   The "tight, no-more-no-less" degree is the irrationality measure `μ(x)`,
   and it splits into three rungs of very different status: (i) the universal
   floor `μ ≥ 2` is **constructive** (Dirichlet pigeonhole — foldable with the
   repo's `Pigeonhole`); (ii) for algebraics the exact value is `2` regardless
   of polynomial degree `d` (Thue–Siegel–Roth) but **ineffectively** — no
   computable constant, no fold receipt; the degree-`d` form schedule
   (`CubeRootTwoCut`'s `k³`) is the generic *effective* receipt, with
   number-specific effective descents (Baker-type, ∛2 down to `≈ 2.47`) paid
   for by transcendence-theory work; (iii) for arbitrary irrationals `x ↦ μ(x)`
   is not computable from the pointing — receipts only squeeze it from both
   sides (presentations witness `μ ≥`, form/measure certificates witness
   `μ ≤`), and the meeting point is generally receipt-less.  The "next term
   below the degree" expansion is real but lives on a **log scale**, not a
   power scale (`|e − p/q| ≍ (log log q / log q)/q²`), matching the lex
   `(height, rate)` ordinal of `CompletabilityGrade`: the refinement axis
   between exponents is ordinal/scale-like.
0′. **Irrational degree + the degree cascade** (originator, second round).
   The degree spectrum is the full continuum: for every real `τ ≥ 2` there are
   reals with `μ(x) = τ` exactly (Jarník; level set has Hausdorff dimension
   `2/τ`), constructible by prescribing CF growth `a_{n+1} ≈ q_n^{τ−2}`.  So
   `μ` is a self-map of `[2,∞]` and the cascade `x ↦ μ(x) ↦ μ(μ(x)) ↦ …` is
   its orbit: generically it collapses (`μ = 2` a.e., then rational, end);
   an infinite nontrivial cascade needs a chain of very-well-approximable
   degrees.  Two 213-native objects fall out: (a) **the self-degree fixed
   point** `μ(τ) = τ` — a number that is exactly its own cut's degree, built
   by a self-referential CF (growth schedule read off the number's own
   approximants); conjecture-grade, a residue-self-pointing shape on the
   degree Lens; (b) **operational cascade = modulus composition**: a schedule
   `N(m,k) = k^e` must *call e's own modulus* to evaluate `⌈k^e⌉`, so
   irrational-degree moduli are receipts taking receipts as arguments — a
   call-tree of folds, formalizable now as a schedule functional consuming a
   `CauchyCutSeq`.  **The functional is BUILT** (`Real213/ModulusComposition`,
   30 PURE): `powSched c B k = ⌈k^{p/2^k}⌉` with `p` read off the exponent cut
   (`dyUp`, sound under integer witness + forward doubling; `rootCeil` exact by
   sandwich), calibrated (`powSched_rat`: integer `s` returns exactly `k^s`),
   instantiated at degree ∛2 (`cbrtPow_at_two = 3` — the ladder eats its own
   degree-3 brick as an exponent) and degree e (`ePow_at_two = 7`, the kernel
   evaluating `eulerCauchySeq.N` inside the schedule), and iterated once:
   `eSelfScheduled` — e rescheduled by a schedule querying e's own modulus,
   limit-preserving (`reschedule_limit_eq`).  **And the degree-as-cut backbone is LANDED** (`powSched_mono`: exponent-cut
   order transports to schedule order, so the threshold "a degree-τ schedule
   suffices for x" is monotone — a cut one level up; its decidability = the
   effective-μ question, Roth-grade).  Still open here: *tightness* of
   `dyUp` (lower witness needs the ratio/rescale property), and a real whose
   *intrinsic* degree is irrational (Jarník construction) rather than a
   rescheduled presentation.
0″. **The `exp(p/q)` instance of the rate-free regime** (cross-branch, proven).
   `ExpLog/ExpUnitModulus`: the unit-fraction family `exp(1/q)` completes through
   the e-generator verbatim (`expUnitCauchySeq`, modulus `k+2`, uniform in `q`),
   and for `p ≥ 2` the factorial presentation provably overtakes
   (`exp_pq_presentation_overtakes`, layer `q+9`; `exp_pq_no_htel` via
   `htel_iff_dominates`) — the sharpest concrete boundary case for rung 1 / the
   dyadic-bracket route: a *transcendental of measure 2* whose natural pointing is
   rate-free.  Whoever builds rung 1 (or the `CubeRootTwoCut`-style schedule for a
   series tail) should test it on `exp(2)` first.  **The fold side is now built**
   (`ExpLog/ExpRationalCut`, 18 PURE): `expPQAb : AbCutSeq` for every `exp(p/q)`
   (`q ≥ 1`), with the doubled-tail upper bracket `S_{N+j} ≤ (a_N(N+1)q + 2p^{N+1})/d_{N+1}`
   past the threshold `2p ≤ (N+2)q` (the geometric halving as one Nat invariant), and
   `e²` localized in `(7, 904/120]` — the ζ(3) posture (fold closed, free modulus
   open) now holds for all rational exp arguments.  The conditional schema is
   instantiated here too (`ExpRationalCut` §5, `expPQCauchySep`): the §3 bracket
   reduces `hsep` to one arithmetic statement per resolution, the strict squeeze
   closing the above-schedule case; open piece = unconditional `hmeas`
   (Padé/Hermite effective irrationality, `I k ≈ 2p/q + O(log k)`).
1. **Graded rate generator** — **CLOSED** (`RateModulus` / `RateStratification`,
   all ∅-axiom).  The margin telescope parametrized by a probe schedule
   `ρ : ℕ → ℕ`: `HtelS a d ρ` (margin `e_i + 1/(ρ_i·d_i)` non-increasing) plus
   one admitted layer (`k ≤ ρ i₀`) ⟹ cut constant past `i₀+1`
   (`rateS_cut_const`).  `ρ = id` recovers `Htel`/`N = k+2` definitionally;
   `ρ = rootFloor s` (new `Meta/Nat/RootFloor`, calibration
   `rootFloor s (k^s) = k`) gives `graded_total_modulus`: **`N(m,k) = k^s + 1`**
   (one better than the conjectured `k^s + 2`).  Per-layer form `DominatesS W d ρ`
   with `htelS_iff_dominatesS` (characterization at every grade) and
   `overtakeS_breaks_layer`.  The forgiven factor, measured at the admission
   layer `i = r^s`, is `r^{s−1}` (slack defended `1/(r·d)` vs the identity
   schedule's `1/(r^s·d)`) — the note's conjectured `i^{s−1}` reads correctly in
   probe units, not layer units.  Strictness witnessed end to end: `sepDen`
   (`d_{i+1} = (⌊√i⌋+2)·d_i`, `W = d`) is root-2-dominated everywhere but breaks
   `Dominates` at layer 4 (`graded_stratification`), and with numerators
   `a_{i+1} = (⌊√i⌋+2)·a_i + 1` (cross-det relation solved over ℕ) the pair
   `sepNum/sepDen` is an actual presentation completing at `N = k²+1`
   (`sep_graded_modulus`) — a real rescued outside the degree-1 class.  Rescue
   is now graded the way `CompletabilityGrade` grades break.  Narrative:
   `theory/math/analysis/holonomic_modulus.md` §4.
   *Post-closure sub-questions*: (a) **schedule comparison law — CLOSED**
   (`dominatesS_schedule_mono` + `schedule_comparison_needs_gap`): a slower
   schedule inherits domination iff, beyond `d` non-decreasing and `ρ' ≤ ρ`,
   the **gap law** holds — `1/ρ'_i − 1/ρ_i ≥ 1/ρ'_{i+1} − 1/ρ_{i+1}`
   (cross-multiplied ℕ form); and the gap law is indispensable (`W≡1, d≡6`,
   layer 2: identity `18 ≤ 18` ✓, root-2 `7 ≤ 6` ✗).  Pointwise the ladder is
   **not a chain**; rungs are independent comparisons, ordered only where the
   gap law holds (it fails inside root-schedule stretches).  (b) **what
   real is `sepNum/sepDen`?** — the witness is synthetic (cross-det relation
   solved over ℕ); its limit's classical identity (CF shape `[0; 2, 3, 3, 4, …]`
   with partial quotients `⌊√i⌋+2`-driven) is uncharacterized, only its
   degree-2-rescued completion is.
2. **Conditional measure-modulus schema** — **CLOSED**
   (`Real213/BracketModulus` + `ExpLog/PiMeasureModulus`, all ∅-axiom).  The
   engine: two-sided bracket (strictly increasing fold + non-increasing upper
   companion + sandwich) + **exclusion depth** `B` ⟹ total modulus
   `N = B k + 2` (`bracket_total_modulus`).  Wallis instance: the companion
   `U_n = W_n·(2n+2)/(2n+1)` is proved decreasing (exact identity
   `4(n+1)²(2n+4)(2n+1) + 2(n+1)(2n+1) = (2n+2)(2n+1)(2n+3)²`), width
   `≤ 2/(2n+1)`; `PiHalfMeasure C s` (probe inside layer `n` ⟹ width
   ≥ `1/(C·k^s)` — the effective measure in pure ℕ bracket form) ⟹
   `n ≤ C·k^s` ⟹ **π/2 modulus `C·k^s + 2`, π modulus `C·(2k)^s + 2`**
   (`halfPi_measure_modulus` / `pi_measure_modulus`).  π is now a *conditional
   degree-`s` modulus real*; the analytic cost (`μ(π) ≤ 7.103`,
   Zeilberger–Zudilin 2020, no effective `(C,s)` formalized) is isolated in the
   single `PiHalfMeasure` inequality.  The conditionality is now proved
   **necessary for this pointing**: `wallis_cross_det` (`W_n = a_n·d_n`, the
   full product — the depth-6 mechanism) ⟹ `wallis_overtakes_every_schedule`
   / `wallis_no_graded_certificate`: domination fails at every layer ≥ 2 for
   **every** positive schedule — the Wallis pointing's **rung is ∞**
   (originator's test question, answered).  Rung is pointing-relative
   (`depth_is_intensional`) — but **no known π pointing sits at a finite
   rung** (corrected 2026-06-10: the earlier "Machin/arctan would sit at
   rung 1" was wrong).  The race needs `tail_i·d_i → 0` (nested
   factorial-grade denominators, e-style); a fixed-ratio geometric pointing
   has `tail·d ≈ const` and never resolves, and Machin-type series inflate
   the common denominator by `lcm(odds) ≈ e²ⁿ`.  A fast pointing improves
   only the **rate⁻¹ factor of the conditional modulus** (log-many layers
   for the same measure hypothesis — e.g. a geometric-width bracket like the
   Catalan/BBP series `π = 3·Σ Catₙ/16ⁿ`, blocked for now on the
   series-limit = Wallis-limit identification, a real-analysis bridge).
   Constructing any rate-carrying π pointing = an effective below-side
   separation for π, transcendence-grade open.  *Residual opening*: prove an
   actual `(C, s)` instance — even a weak one (any effective
   transcendence-measure bound for π) — turning the conditional modulus
   unconditional.
3. **Two-real separation modulus** — the genuine `N(m1,k1)×N(m2,k2)` object:
   deciding `x ≤ y` for two folds needs a joint `|x−y|` lower bound.  The
   one-probe gap quantum `1/(k·d_i)` is already bilinear (probe × convergent,
   the Farey/Stern-Brocot `det = ±1`); the two-fold version is new machinery
   (`cutLe` currently sidesteps it).
4. **Higher algebraic instances** — degree-4+ form cuts (e.g. `√2+√3`,
   `x⁴−10x²+1`), and the cubic-unit narrative: at degree 2 the binary form
   carries an infinite unit orbit (Pell, `W ≡ 1` floor); at degree 3 the binary
   slice of the rank-1 unit orbit is finite (Thue/Delaunay–Nagell — hard), the
   orbit needing the full rank-3 lattice.  Why the self-similar P-orbit story
   does not lift to degree 3 as binary dynamics.

0‴. **The CF pointing is universally rate-carrying — packaged + first transcendental
   instance** (cross-branch follow-up).  `cf_universal_total_modulus` (already in
   `ContinuedFractionModulus`) is now packaged with the explicit constant into
   `cfCauchySeq : CauchyCutSeq` (`N(m,k) = k+2`, §6), and instantiated at
   **Lambert's `coth(1/q) = [q; 3q, 5q, …]`** (`cothUnitCFCauchySeq`, anchors
   `21/16`, `coth(1) ∈ (5/4, 3/2]`) — the repo's first *transcendental* completed
   through its CF, unconditionally.  The pointing dichotomy is now a theorem pair:
   the series pointing of `exp(p/q)` (`p ≥ 2`) carries no rate (`exp_pq_no_htel`),
   the CF pointing of the same number family carries everything.  **The weld** —
   Lambert CF correctness (Padé/Bessel identity: the CF real = series `coth(1/q)`)
   — is the remaining identity; once welded, `e^{2/q} = (coth(1/q)+1)/(coth(1/q)−1)`
   is one cut-Möbius step, discharging `ExpRationalCut`'s measure hypothesis on the
   sharpest route.

0⁗. **The weld, stage 1 — the series side of the Lambert ladder is built**
   (`ExpLog/LambertWeld.lean`, 7 PURE).  The Bessel contiguity
   `F_{n−1} = (2n+1)Fₙ + u·F_{n+1}` (`f_n(j) = 1/((2j)!!(2n+2j+1)!!)`, coefficient
   identity `(2n+1)+2j = 2n+2j+1`) is delivered **division-free at every truncation**:
   `FNum q n J` (Horner: `FNum(J+1) = (2J+2)(2n+2J+3)q²·FNum(J) + 1`) with
   `weld_ladder : (2n+2J+3)·FNum n J = (2n+3)·FNum (n+1) J + 2J·FNum (n+2) (J−1)`,
   and the bottom rungs collapse to cosh/sinh exactly (`(2j)!!(2j−1)!! = (2j)!`):
   `weld_base` (cosh enters at `n = −1`), `sinhNum_eq_FNum_zero` (`n = 0` IS sinh).
   So `coth(1/q) = q·F_{−1}/F_0` and the unrolled ladder IS `[q; 3q, 5q, …]`.
   **Stage 2 — ✅ the finite weld identity is PROVEN** (`LambertWeld` §4–§6, module
   22 PURE): the pairing functional `PF` (`[P(u)·F_m]|_J` cleared, Horner: the
   `u`-shift costs exactly `2J·(2m+2J+1)` and drops `J` by one), the lifted ladder
   `pf_ladder` (same shape as `weld_ladder`, uniform in the polynomial — the tail
   reduces to itself one level down), the convergent polynomials `AP`/`BP`
   (`Ã/B̃`, list recursion), and the **matrix-unrolling rows**

     `vFac J n · coshNum q J = [Ã_{n−1}F_n]|_J + 2J·[Ã_{n−2}F_{n+1}]|_{J−1}`
     `v0Fac J n · sinhNum q J = [B̃_{n−1}F_n]|_J + 2J·[B̃_{n−2}F_{n+1}]|_{J−1}`

   (`weld_pair_cosh`/`weld_pair_sinh`, exact at every truncation, division-free;
   `n = 0` rungs are `weld_base`/`sinhNum_eq_FNum_zero`; each step is one
   `pair_step` = ladder + linearity, matching the `AP/BP` recursion exactly).
   This IS the CF-correctness identity `(F_{−1}, F_0) = M₀⋯M_{n−1}·(Fₙ, F_{n+1})`
   of the Lambert fold.  **Stage 3a — ✅ the evaluation bridge is PROVEN**
   (`LambertWeld` §7, module 36 PURE): descending Horner evaluation `dev`
   (`hornEv` with the defeq-clean `c + q²·acc` accumulator), the list algebra
   (`dev_lsmul`, `dev_ladd_eq`, `dev_ladd_succ` with the padding power `q²`,
   parity length lemmas `AP_BP_length`), and **`cf_bridge`**:
   `cfPn (cothCF q) (2k) = q·dev (AP (2k+1))`, `cfPn (2k+1) = dev (AP (2k+2))`,
   `cfQn (2k) = dev (BP (2k+1))`, `cfQn (2k+1) = q·dev (BP (2k+2))` — the
   equivalence transform `[q; 3q, 5q, …] ↔ 1 + u/(3 + u/(5 + …))` as four `Nat`
   identities (4-way parity induction riding the `AP/BP` recursions;
   `decide`-anchored at `q = 2`).  The CF fold and the cosh/sinh partial
   numerators now live in ONE identity system (weld rows §5 + bridge §7).
   **Stage 3b — ✅ the series side is a fold and the pointings meet on probes**
   (`CothSeriesCut.lean`, 17 PURE): the truncated coth ratio
   `T_J = (2J+1)q·coshNum_J/sinhNum_J` climbs — the cross identity `tcross_id`
   cancels the `q²`-terms exactly, leaving `(2J+3)sinh − (2J+1)cosh ≥ 0`
   (`cosh_le_sinh`, termwise) — so `cothSeriesAb q : AbCutSeq`.  At `q = 1` the
   CF fold's completed limit and the series fold's layer cuts **agree on the
   bracket probes** `(5/4, 3/2]` (`two_pointings_agree`; series side: the
   uniform bound `2(2J+1)coshNum + 1 ≤ 3·sinhNum`, margin recursion
   `X_{J+1} = (2J+2)(2J+3)X_J − (4J+3)` safe from `X_0 = 1`).
   **Stage 3c prep — ✅ the row determinant collapses** (`LambertWeld` §8 +
   `CothSeriesCut` §5): `row_det` — multiplying the cosh row by the sinh pairing
   and vice versa, the head products `X_A·X_B` cancel **exactly**:
   `(vFac·cosh)·X_B − (v0Fac·sinh)·X_A = 2J·(Y_A·X_B − Y_B·X_A)` (additive form
   proven) — the order comparison is governed entirely by the `2J`-tail cross;
   plus `vFac_eq` (`vFac = (2J+1)·v0Fac`, the `T_J`-scaling link), `FNum_pos`,
   `PF_head_le`, and the **first instance of the upper transfer**:
   `coth1_lt_4_3` ⟹ `T_J <` the first odd convergent `4/3` uniformly (same
   margin induction as the `3/2`-bound; the series cut reads `true` at `4/3`
   at every layer).  **Stage 3c, base + choice-function inputs — ✅**
   (`CothSeriesCut` §6): `coth_lt_first_odd` — `T_J` below the first odd
   convergent `r₁ = (3q²+1)/(3q)` for **every** `q`, margin recursion with
   slack `4J(J+1)q²` from the exact base `X_0 = 1` (cut level:
   `coth_series_below_r1`); `t_mono_strict` — the climb is strict (the explicit
   positive increment the choice functions consume).
   **Stage 3c core (remaining; fully scoped)**: the sup-equality needs two
   cross-system uniform families — (A′) `T_J ≤ r_{2i+1}` ∀i (only `i = 0` is
   margin-inductive; the family needs the rows) and (A) `r_{2k} ≤ U_J` (upper
   companion); given them the transfers follow by gap/increment choice
   functions (CF gaps from `cf_det`/`cf_even_det`, T-increments from
   `t_mono_strict`).  Via `row_det` the families reduce to the tail-cross
   sign, which by the shared-weight structure (`X_A, X_B` share
   `R·FNum`-weights; the per-step weight ratio is `[F−1]/F` — monotone for
   free) is a **Chebyshev rearrangement over the coefficient minors of
   `(AP, BP)`** (parity-signed, `cf_det`-style induction expected) — **The engine is
   now BUILT** (`LambertWeld` §9, no ΣΣ infra needed): the γ-coupling dissolves
   because the mixed-head terms reduce *exactly* to weight dominance of the
   pointwise **gap list** (`b₀·as = a₀·bs + g`): `weight_dom` (the transported
   `PF`-weight system is dominated by the `dev`-system scaled by `FNum` — per
   step it is the `FNum` recursion minus its `+1`; holds for every list, no
   hypotheses) + `cross_le` (`PF a·dev b ≤ dev a·PF b` under `MinorLE a b`,
   two list inductions; gap recovery via `lsub`/`ladd_lsub_recover`).
   **The minor sign is now PROVEN** (`LambertMinor`, 10 PURE): at the
   position-function level (`apF/bpF`, totalized by `0` off support — no list
   edge cases), the closed **4-family system** `minorSys n = {m₁ adjacent
   minors, D same-position cross-level, F one-apart, G reverse one-apart}`
   closes by two-step strong induction, every step **termwise** (no
   cancellation) after the bilinear `ring_nat` expansion of the three-term
   recursion; the two-apart cross `E` that `m₁`'s step needs is *derived* on
   demand (`ratio_chain` through the pivot `bpF (n+1) (t+1)`, zero-pivot case
   free by prefix-support `bpF_support`) — this kills the infinite m₂/m₃/…
   ladder that a naive gap-indexed family would open.
   **The plumbing is CLOSED** (`LambertOrder`, 36 PURE): `minor_all` (all-gap
   minors), `nth`-transport onto the weld lists, zero-pad lemmas, and the full
   **(A′) assembly** — `series_le_odd`: `T_J ≤ p_{2i+1}/q_{2i+1}` for every
   `q, i, J` (`cross_le` twice, chained through the `dev (AP (2i+1))` pivot by
   the det-one floor `dev_cross_det`).  **W1 closed at the limit level**
   (`cf_limit_false_of_series_false`): a strict series reading + the unit
   odd–even gap squeeze the even convergent past the probe at the explicit
   choice layer `L = k·s_J + k + 2`.
   **`e^{2/q}` cut-Möbius CLOSED — `exp(2/q)` completes unconditionally**
   (`ExpMoebius`, 20 PURE): the odd convergents under `z ↦ (z+1)/(z−1)` climb
   with cross-det exactly `2·a_{2L+3}` (the Möbius doubles the det-one floor);
   `dN = p − q` obeys the same three-term recurrence, so the universal rate
   machinery applies verbatim: `expTwoOverQCFCauchySeq`, total modulus `k+2`,
   no hypotheses beyond `q ≥ 1`.  `e² ∈ (22/3, 37/5]`, sharper than the series
   bracket.  The *series* presentation's `hmeas` is **dodged, not assumed** —
   rate is a property of the pointing, not the real.
   **The weld closed modulo ONE brick** (`LambertOrder` §7–§8): the lower
   transfer climbs in `J` for free (`lower_step`; side condition = every even
   convergent below the first odd one), `i = 0` closed outright, so the whole
   lower family reduces to its **matched-truncation base** `LowerBase`:
   `devA(2i+1)·s_{2i+1} ≤ (4i+3)·devB(2i+1)·c_{2i+1}` — the Padé flip at
   `J₀(i) = 2i+1`.  Given `LowerBase`: `W2`, the series fold completes
   (`cothSeriesCauchySepOfBase`, schedule `I k = 2(k+2)+1`, certificate
   `W2 ∘ W1`), and `weld_limit_agreement` — the two pointings of `coth(1/q)`
   agree on every probe.
   **The open brick — `LowerBase` — now has a VERIFIED PROOF BLUEPRINT**
   (`lowerbase_blueprint.md`): a multi-agent derivation round produced (1) the
   **weld Casoratian** `R_{J+1}M_J = R_JM_{J+1} + K_J` with `K_J` = the
   `tcross_id` quantity (unimodular `i`-evolution; flip criterion + ratio
   descent), and (2) the **master identity** (the untruncated Padé remainder,
   coefficientwise, proven by the constant-weight-ratio double recursion with
   the absorption `(2n+2m+5) = (2n+3)+(2m+2)`), giving sliver closed forms,
   flip leading coefficient `(4i+2)!!`, and a **t-coefficientwise dominance**
   (`t = q²−1`) with ≥ 10× slack — the 1.0098-tight coupling crunch dissolved.
   All claims re-verified by exact symbolic computation.  Remaining:
   formalization only (next marathon; plan in the blueprint note).
   (Lean: core `Nat.pow_add` and `Nat.le_of_add_le_add_right` are
   `propext`-dirty — `pow_add_two` via the definitional `pow_succ` chain;
   NatHelper's left-cancel + `add_comm`.)
   Lean note: PolyNatM's normalizer does **not** drop `0·atom` monomials and chokes
   on un-reduced `(J+1)−1` index atoms — close `J = 0` rungs by `rfl` (all-literal
   defeq) and re-ascribe IHs with reduced indices.

## The 213 reading

The fold/residue correction refines from a dichotomy into a **filtration**:
modulus degree = how many receipts the pointing carries (0 = the form is the
cut; 1 = the rate is its own receipt; s = receipt-of-receipt; no finite degree
= toward reached-by-none).  Residue-lint: this is a Lens-grading of
*pointings*, not an ontological stratification of the residue — the residue
sits in no rung; the ladder classifies the ways of pointing at it.

## Pointers

- Closed: `lean/E213/Lib/Math/NumberSystems/Real213/CubeRootTwoCut.lean`,
  `PhiAsCut`/`FibCassiniNat` (degree 2), `holonomic_modulus.md` (degree-1 class);
  rung 1: `Real213/{RateModulus,RateStratification}.lean` (graded generator,
  `HtelS`/`DominatesS`/`graded_total_modulus`) + `Meta/Nat/RootFloor.lean`
- Break-grading: `CompletabilityGrade`, `RefinedCompletabilityEngine`
- ζ(3) companion frontier: `zeta3_free_modulus.md`
