# Holonomic modulus — completeness as a constructed convergence rate

**Status**: Closed.  Source of truth: `lean/E213/Lib/Math/NumberSystems/Real213/{RateModulus,
HolonomicReal,ExpLog/EulerModulus,ExpLog/EulerCertifiedBracket}`, all ∅-axiom.

A Real213 real is a decision procedure against ℚ; completeness is not constitutive
but a *limit operation* on convergent sequences (`completeness_relocated.md`).  A
sequence completes by a **modulus** `N : ℕ → ℕ → ℕ` with `N m k` the index past which
the convergent cut at threshold `m/k` no longer moves.  The classical picture supplies
that modulus by a choice principle; here it is a *constructed value* — for a large
class of reals, derived from the convergence rate itself.  This chapter is the general
mechanism and its instances.

## 1. The rate criterion

Write the convergents as `aᵢ/dᵢ` (`aᵢ, dᵢ : ℕ`, `dᵢ ≥ 1`), monotone increasing to the
real.  At index `i` two quantities meet at a threshold `m/k`:

  - the **denominator-gap quantum**: if `m/k ≠ aᵢ/dᵢ` then `|m/k − aᵢ/dᵢ| ≥ 1/(k·dᵢ)`
    (the integer cross-difference `|m·dᵢ − k·aᵢ| ≥ 1`);
  - the **tail rate**: `|real − aᵢ/dᵢ|`.

> **Criterion.**  The cut has a *free* total modulus `N(m,k) ≈ k` exactly when the
> tail beats the gap quantum at index `≈ k`: `tailᵢ · k · dᵢ < 1` for `i ≳ k`.

When it holds, the convergent at index `≈ k` lands strictly on the real's side of
`m/k`, the side is read off a decidable `Bool`, and no irrationality measure is
needed.  The divide it draws is **rate-carrying vs rate-free**, *not*
algebraic-vs-transcendental: a real presented with a fast enough rate completes
unconditionally; one presented without keeps deferring.

## 2. The general generator

The criterion is realised by a margin invariant.  Carry `eᵢ + 1/(i·dᵢ) ≤ m/k`
(cross-multiplied to ℕ as `RInv`).  If the margin is **non-increasing** — the rate
certificate

> `Htel a d : ∀ i ≥ 1, (a_{i+1}·(i+1)+1)·(i·dᵢ) ≤ (aᵢ·i+1)·((i+1)·d_{i+1})`

— then the invariant is preserved by *pure transitivity* (no recurrence, no `ε`-`δ`),
and the cut is constant past `k+2`:

> **`RateModulus.rate_total_modulus`** *(∅-axiom)*.  For monotone convergents `a/d`
> with `Htel a d`, `hmono` (increasing), and `hmonoS` (strictly increasing), every
> `(m,k)` with `k ≥ 1` has a total modulus `N(m,k) = k+2`: `rcut a d i m k =
> rcut a d j m k` for all `i, j ≥ k+2`.

The three regimes at index `k+1` are decided by a `ℕ`-trichotomy on `a_{k+1}·k` vs
`d_{k+1}·m`: strictly below ⟹ the cut stays `true` (the margin invariant, `rinv`);
equal ⟹ `false` from `k+2` (strict monotonicity crosses the threshold); above ⟹
`false` from `k+1`, forward by monotonicity (`false_fwd`).

`Htel` itself has a closed form in the **cross-determinant** `W_i = a_{i+1}·d_i −
a_i·d_{i+1}` — the divergence ladder's central object:

> **`RateModulus.Htel_of_crossdet`** *(∅-axiom)*.  Given `W` with `a_{i+1}·d_i =
> a_i·d_{i+1} + W_i`, the rate certificate holds as soon as `i(i+1)·W_i + i·d_i ≤
> (i+1)·d_{i+1}` — the cross-determinant is small relative to the denominator's
> discrete growth.

This is the bridge where the depth arc (the cross-determinant `W` of
`completeness_without_completeness.md` Part III) meets the modulus generator: `Htel`
*is* a smallness law on `W`.

This is the *unconditional real* API: a generator-built real coerces to a valid cut
with the modulus a field, not an assumption.  Its typed home is `HolonomicReal`
(`HolonomicReal.cut_valid`).

## 3. Instances

**φ — algebraic (`HolonomicReal.phiHolonomicReal`).**  The golden ratio's Pell/
Fibonacci convergents *equal* the closed-form golden cut past index `2k`
(`PhiCauchyLimit`), so the modulus is the exact `N(m,k) = 2k`.  Order-2, constant
coefficients (`det = 1`) — the depth-floor of the divergence ladder
(`DepthFloorDetOne`: the floor is the P-orbit invariant).

**e — structured transcendental (`ExpLog/EulerModulus`).**  `e = Σ 1/k!` has
convergents `aᵢ/i!`.  The margin step reduces to `i(i+2) ≤ (i+1)²` (i.e. `0 ≤ 1`,
discharged by the `Meta.Nat.PolyNat` reflection ring); the factorial tail
`1/(i·i!)` beats the gap quantum `1/(k·i!)` at `i ≥ k` (ratio `k/i < 1`).  Hence

> **`euler_total_modulus`** *(∅-axiom)*: `N(m,k) = k+2`, and **`eHolonomicReal`** — e
> is a complete `HolonomicReal` with a constructed modulus, on the same footing as φ.

e satisfies the abstract certificate (`euler_Htel`, `euler_hmono`, `euler_hmonoS`),
and `euler_cut_const` / `euler_total_modulus` are *direct instances* of
`rate_cut_const` — e carries no bespoke engine of its own; the generator does the
work once.
`eHolonomic` is the genuine order-1 recurrence (`eHolonomic_recurrence`:
`eulerDen (n+1) = (n+1)·eulerDen n`, coefficient `(n:ℤ)+1`), so the bundle's
recurrence actually generates its convergents.

The elementary witness form — e certified on its proven bracket `(8/3, 3)` directly
from the bounds — is `ExpLog/EulerCertifiedBracket`.

**∛2 — algebraic degree 3, the form-margin mechanism (`CubeRootTwoCut`).**  The
algebraic instances do not need the rate race at all: the side-decision against a
probe `m/k` reduces to the all-additive comparison `ε_i·k³ < d_i³`, where the
degree-3 form margin `|m³ − 2k³| ≥ 1` arrives as the `+1` of `Nat` strictness and
`ε_i` is the presentation's cube-slack.  With the dyadic bisection presentation
(`cbrtNum i / 2^i`, slack `≤ 24·4^i` vs `d³ = 8^i`) the total modulus is
`N(m,k) = 3k+5` (`cbrtCauchySeq`), and the completed fold lands exactly on the
frozen closed-form cut `decide (2k³ ≤ m³)` (`cbrt_limit_eq_form`) — the degree-3
analog of φ's `masterCut` story (`FibCassiniNat.qb_lt_pk`'s `4k² < b²` is the
degree-2 shadow of the same `ε·k^s < d^s` schema).  The algebraic degree enters
as the probe exponent `k^s` in the schedule, and the form makes the modulus
presentation-robust; the rate-carrying / rate-free divide of this chapter is the
transcendental-only regime.

## 4. Frontier

**π via Wallis is rate-free — at every grade, provably — and conditionally
priced.**  The Wallis cross-determinant is the *full product* `W_n = a_n·d_n`
(`wallis_cross_det`: `(2n+1)(2n+3)+1 = 4(n+1)²` — the same mechanism as the
presentation's divergence depth 6), so scheduled domination fails at every
layer `n ≥ 2` for **every** positive schedule
(`PiMeasureModulus.wallis_overtakes_every_schedule`,
`wallis_no_graded_certificate`): the Wallis pointing sits beyond every rung of
the graded ladder — a theorem, not an estimate.  Deciding the side therefore
needs a lower bound on
`|π/2 − m/k|` — π's irrationality measure (`μ(π) ≤ 7.1`, genuinely hard).
And no *known* π pointing escapes this: the margin race needs the tail to
shrink against the **probe-weighted** quantum `1/(ρ_i·d_i)`, i.e.
`tail_i·d_i → 0` — factorial-grade *nested* denominator growth, as in e
(`tail·d = 1/i`).  A fixed-ratio geometric pointing has `tail·d ≈ const`
(the race never resolves with depth), and Machin/arctan-type series
additionally inflate the common denominator by `lcm(odd ≤ 2n+1) ≈ e²ⁿ`.  So
"fast" alone does not buy the free modulus; what a fast pointing buys is the
**bracket width per layer** — the rate⁻¹ factor of the *conditional* modulus
(logarithmically many layers instead of polynomially many, for the same
measure hypothesis).  Constructing any genuinely rate-carrying π pointing
would yield an effective below-side separation for π — open,
transcendence-grade.  This is the rate-free posture of `PiCut`, not a
property of transcendence.  What the conversion law *can* do is price the missing measure
exactly (`ExpLog/PiMeasureModulus` + the engine `BracketModulus`): the Wallis
fold has a decreasing upper companion `U_n = W_n·(2n+2)/(2n+1)` (a per-layer
shrinking bracket, width `≤ 2/(2n+1)`), and the single hypothesis
`PiHalfMeasure C s` — any probe still inside the layer-`n` bracket forces width
`≥ 1/(C·k^s)`, the effective measure in pure ℕ form — yields the constructed
total modulus `N(m,k) = C·k^s + 2` for π/2 and `C·(2k)^s + 2` for π.  π moves
from "completion modulus as opaque hypothesis" to "conditional degree-`s`
modulus": rate⁻¹ ∘ distance with the distance certificate named, isolated, and
awaiting its `(C, s)` instance.

**The holonomic class, via the cross-determinant.**  `Htel_of_crossdet` reduces the
rate certificate to a smallness law on the cross-determinant `W` — exactly the object
the divergence ladder studies.  e instantiates it directly: e's cross-determinant
*is* `eulerDen` (`euler_cross_det`: `eulerNum (n+1)·eulerDen n = eulerNum n·eulerDen
(n+1) + eulerDen n`), and the smallness condition collapses to `i(i+1)+i ≤ (i+1)²`
(i.e. `0 ≤ 1`).  So `euler_Htel` is *derived from the cross-determinant*, not from a
bespoke estimate — the depth arc and the modulus generator are one mechanism.  What
remains for another fast holonomic real is just its `W` and the smallness check
`i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`; the rate-free reals (π via Wallis) are exactly
those whose `W` grows too fast for it.

**ζ(3) sits at the boundary, presentation-dependently** (`Real213/Zeta3Cut`).  The
Apéry convergents are built as an exact ℕ orbit of the degree-3 recurrence
(`aperyOrbit_exact`), with closed-form cross-determinant `W_m = 6·(m!)⁶`
(`zeta3_cross_det`) and the bracket `601/500 < ζ(3) ≤ 1203/1000`; but in the
factorial-cleared presentation that `W` *overtakes* the denominator quantum at
layer 9 (`zeta3_presentation_overtakes`, via `overtake_breaks_layer`) — rate-free,
so the completion modulus stays a hypothesis there, as for π/Wallis.  The
rate-carrying ζ(3) presentation is the reduced one (`2·lcm(1..n)³·bₙ`
denominators, tail `α⁻²ⁿ` with `α = (1+√2)⁴`, and `e³ < α` makes the criterion
hold); its ∅-axiom construction costs exactly the classical Apéry arithmetic
(reduced-numerator integrality, `lcm(1..n) < 3ⁿ`) and is an open frontier.

**The smallness law is a stratification — `W` against `d`, layer by layer.**  Making
the smallness condition the primitive object turns completeness into a comparison of
two tower-internal growth axes, read at every layer
(`Real213/Modulus/RateStratification.lean`).  Write `Dominates W d i` for "the
cross-determinant stays below the denominator's growth quantum at layer `i`":
`i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`.  Then

> **`htel_iff_dominates`** *(∅-axiom)*.  The rate certificate `Htel a d` holds **iff**
> every layer `i ≥ 1` is dominated.

This upgrades `Htel_of_crossdet` from an implication to a characterization:
completability *is* the W-vs-d comparison, read at every layer — not a yes/no fact
about an individual real.  Domination everywhere gives the free modulus
(`dominated_free_modulus`, via `rate_total_modulus`); conversely **any** layer where
`W` overtakes the denominator quantum, `(i+1)·d_{i+1} < W_i`, breaks domination
there (`overtake_breaks_layer`) — the abstract overtake boundary, no irrationality
measure, just the two growth axes flipping order.

The **unimodular det-1 floor** is the trivially-free bottom of this stratification.
`DepthFloorDetOne` shows the P-orbit's convergent cross-determinant is the constant
`W ≡ 1` (the invariant of `T = [[2,1],[1,1]]`, `det T = 1`); against the denominator
`d_i = (i+1)(i+2)` the comparison `i(i+1)·1 + i·d_i ≤ (i+1)·d_{i+1}` collapses to
`i ≤ i+2` (`floor_dominates_all`).  So any presentation whose cross-determinant is the
unimodular floor carries its own rate certificate unconditionally
(`floor_carries_Htel`).  The atomic floor is the free bottom; the overtake regime is
the genuine content above it.  `tower_stratification` bundles the three facts.

**The comparison is graded, not binary — the generator takes a probe schedule.**
The margin invariant of §2 never used the specific slack `1/(i·dᵢ)`; it used only
that the slack telescopes and that some layer's slack absorbs the probe's `Nat`
strictness quantum `1/(k·dᵢ)`.  Parametrize it: a **probe schedule** `ρ : ℕ → ℕ`
carries the margin `eᵢ + 1/(ρᵢ·dᵢ)`, the graded certificate `HtelS a d ρ` says it
is non-increasing, and probe denominator `k` is *admitted* at any layer `i₀` with
`k ≤ ρ i₀`.  Then (`RateModulus.rateS_cut_const`, ∅-axiom) the cut is constant
past `i₀ + 1` — the same trichotomy, pure transitivity again.  The identity
schedule is §2 verbatim (`Htel` is definitionally `HtelS a d id`, `N = k+2`).
The degree-`s` root schedule `ρ = rootFloor s` (`Meta/Nat/RootFloor`, the integer
root with `rootFloor s (k^s) = k`) admits `k` at layer `k^s`, giving

> **`RateModulus.graded_total_modulus`** *(∅-axiom)*.  `HtelS a d (rootFloor s)`
> plus the monotonicity pair yields the total modulus `N(m,k) = k^s + 1`.

What is bought and what is paid is visible at the admission layer `i = r^s`: the
identity schedule defends the slack `1/(r^s·dᵢ)` there, the root schedule only
`1/(r·dᵢ)` — an `r^{s−1}` factor of overtake forgiven per probe — and the price
is the modulus degree `k^s`.  The per-layer form is `DominatesS W d ρ i`
(`ρᵢ·ρ_{i+1}·W_i + ρᵢ·dᵢ ≤ ρ_{i+1}·d_{i+1}`), and the characterization persists
at every grade: `htelS_iff_dominatesS` (the graded certificate **iff** scheduled
domination at every layer), `overtakeS_breaks_layer` (the scheduled overtake
boundary).  The grading is **strict**: the presentation `d_{i+1} = (⌊√i⌋+2)·dᵢ`
with `W = d` is dominated by the root-2 schedule at every layer yet breaks the
identity-schedule comparison at layer 4 (`sep_dominatesS_all` /
`sep_breaks_unit_schedule`, bundled in `graded_stratification`) — and the
witness is an actual real, not just a predicate pair: the numerators
`a_{i+1} = (⌊√i⌋+2)·a_i + 1` solve the cross-det relation over ℕ exactly
(`sep_cross_det`, `W = d`), and `sep_graded_modulus` completes `sepNum/sepDen`
through the degree-2 schedule with the constructed modulus `N(m,k) = k² + 1`,
its degree-1 certificate broken.

This lone degree-2 witness is not the ceiling: `RateHierarchy` promotes it to a
**uniform family** `sepDenS s` (`d_{i+1} = (⌊i^{1/s}⌋+2)·dᵢ`, `W = d`;
`sepDenS 2 = sepDen`).  `sepDenS_dominatesS_all` is the degree-`s` rescue at
every layer — the *same* root-monotonicity argument, now parametric.  The break
generalizes too: `sepDenS_breaks` shows that for every `t ≥ 2`, the
degree-`(t+1)` presentation fails the degree-`t` schedule at the perfect
`t`-th-power layer `(t+3)^t` — there both schedule probes read `t+3` while the
denominator's growth coefficient is pinned below `t+1` by the **cross-degree
power gap** `(t+3)^t < (t+2)^{t+1}` (`Meta.Nat.PowBernoulli.pow_pred_lt`, an
additive-Bernoulli consequence: the degree axis genuinely outruns the base
axis).  Together (`strict_modulus_hierarchy`) every consecutive integer rung
`(t, t+1)` is separated by an explicit presentation, so the ladder is **infinite
and strict**; `sepS_graded_modulus` occupies each rung with an actual real of
modulus degree exactly `t+1`.

The bottom rung, dually, is **generously inhabited**: degree 1 is not the
unimodular `W ≡ 1` floor alone.  `RateHierarchy.fastDen_dominates` shows that for
*any* cross-determinant `W` — however large, even unbounded — the denominator
`d_{i+1} = i·W_i + d_i` is degree-1 dominated at every layer.  What decides the
degree is the **race between `W`-growth and `d`-growth per layer**, not the size
of `W`.  The concrete witness is e: its factorial presentation has cross-determinant
`W = eulerDen = i!` (unbounded) yet completes at `N = k+2` (`EulerModulus`), because
the per-step denominator ratio `(i+1)` outruns it — where `sepDen`'s slower ratio
`⌊√i⌋+2` against the same `W = d` lands at degree 2.  This is good news for
*constructing* reals — a cheap term-count modulus needs only fast denominators,
not the optimal continued fraction — with the honest caveat that the cost does
not vanish but relocates into the *size* of each term (`d_i = i!`).  So "completes
freely" is not one comparison but a ladder of them, one per schedule — *rescue*
is graded the way `CompletabilityGrade` grades *break*, and the modulus degree is
the rung's price.  This is the conversion law of the modulus-degree ladder read
inside the generator itself: degree of the modulus = (distance certificate) /
(rate of the pointing), with the schedule the dial between the two.

### 4.1 The modulus-degree calculus (closed)

The ladder is now a small calculus, four facts pinning what the degree *is* and
how it behaves.

**What fixes the degree** (`DegreeCriterion`).  Dividing the degree-`s` domination
by `ρ_{i+1}` (the schedule monotone) brackets it between two clean inequalities
differing only by the single term `d_i`: it is **sufficient** that the probed
cross-determinant fit under the denominator *increment*,
`⌊i^{1/s}⌋·W_i + d_i ≤ d_{i+1}` (`dominatesS_of_scheduled_increment`), and
**necessary** that it fit under the *next denominator*, `⌊i^{1/s}⌋·W_i ≤ d_{i+1}`
(`scheduled_le_of_dominatesS`).  So the degree is exactly the race between the
*probed* cross-determinant `⌊i^{1/s}⌋·W_i` and the denominator's growth — not the
size of `W`.  The criterion is monotone in the degree (`rootFloor_antitone_degree`:
a larger `s` is a slower probe; hence `increment_criterion_mono`), so the degree
ceiling is well-defined and upward-closed, and the degree-1 boundary
`i·W_i + d_i = d_{i+1}` is saturated exactly by `fastDen` and e.

**Comparing two reals** (`RateComparison`).  Promoting the rational probe `m/k` to
a second convergent, the joint comparison `a_i/d_i ⋚ b_j/e_j` is the
**two-convergent cross-determinant** `a_i·e_j − b_j·d_i` (the single-probe
Farey/SL₂ determinant, doubled).  Given an apartness witness `m/k` — a rational the
first cut sits below and the second above — the comparison is settled for all
`i, j ≥ k+2` (`two_real_separation_modulus`), the two single moduli composing by
`max`.

**Arithmetic** (`RateArithmetic`).  The cross-determinant factors through the
summands: `W^{x+y}_i = W^x_i·e_i e_{i+1} + W^y_i·d_i d_{i+1}` (`sum_cross_det`),
`W^{xy}_i = a_i d_{i+1}·W^y_i + b_i e_{i+1}·W^x_i + W^x_i W^y_i` (`prod_cross_det`).
Read off these, degree is **not additive**: the naive common-denominator sum carries
the *other* denominator quadratically, so mismatched growth (`d_{i+1} < e_i`) makes
it rate-free at *every* degree (`sum_naive_not_dominatesS`) even when both summands
are degree 1 (`e + e` over `(i!)²` is rate-free, though `2e` is degree 1 by
scaling).  The clean closure is on a **shared denominator**, where the
cross-determinants simply **add** (`matched_sum_cross_det`: `W^{x+y} = W^x + W^y`, no
inflation) and `x + y` is degree ≤ `s` exactly when the probed cross-determinants
*jointly* fit the shared increment (`matched_sum_dominated`) — "each summand at
degree `s`" being a factor of 2 short.  Degree, throughout, is a property of the
*pointing*, not of the real: the same lesson as `object1_not_surjective`, now
quantified.

## 5. The thesis, completed

"Completeness is a relocated finite operation" becomes fully constructive for the
rate-carrying class: the limit object is a decidable cut, its modulus a constructed
function of the convergence rate, and the algebraic floor (φ) and the structured
transcendental (e) are the *same kind* of object — each a `HolonomicReal` whose
recurrence carries its own rate.  The only reals that still take the modulus as a
hypothesis are the rate-free presentations, and that is a deficiency of the
*presentation*, not of the real.

The smallness condition `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}` (`Htel_of_crossdet`) is
the comparison of the cross-determinant axis against the denominator axis;
`tower_native_completeness.md` closes that comparison — the overtake boundary, the
Liouville adjudication (`W = d`), closure of the finite-coordinate class, the
coordinate generator, and the tie to the residue.
