# The degree of a number

The degree of a number is not a property of the number.  It is the growth
class of the receipt a *pointing* carries — and the number's "own" degree is
the threshold of those classes: a cut one level up, reached by its receipts
the way a real is reached by its convergents.

## 213-native answer

A `Real213` real is a decidable cut; completing a pointing at it costs a
modulus `N(m,k)` — the index past which the layer cut at probe `m/k` stops
moving (`theory/math/analysis/holonomic_modulus.md`).  The **degree** of a
pointing is the growth class of its `N` in `k`.  The repo's ladder, each rung
a theorem: degree 0 — the form is the cut, no layers at all (φ's `masterCut`;
∛2's `decide (2k³ ≤ m³)`, `Real213/CubeRootTwoCut.cbrt_limit_eq_form`);
degree 1 — the rate is its own receipt (`N = k+2` for e and the Liouville
constant, `N = 2k` for φ, `N = 3k+5` for ∛2's bisection); composed degree —
the exponent slot itself holds a cut, and the schedule queries that cut's
modulus to evaluate (`Real213/ModulusComposition.powSched`, with `ePow_at_two`
running e's modulus inside the schedule); no finite degree — the pointing's
cross-determinant overtakes its denominator and the modulus stays a
hypothesis (`Zeta3Cut.zeta3_presentation_overtakes`, the π-posture).

## Derivation

Two mechanisms pay for a degree (`theory/math/analysis/form_margin_modulus.md`).
The **form margin** is algebraic: a degree-`s` integer form vanishing at the
real turns every side-decision into `ε·k^s < d^s`, the `+1` of `Nat`
strictness supplying `|F(m,k)| ≥ 1` for free — `4k² < b²` at `s = 2`
(`FibCassiniNat.qb_lt_pk`), `ε·k³ < d³` at `s = 3` (`cbrt_false_side`).  It is
presentation-robust: any pointing with a slack rate completes.  The **rate
race** is the transcendental regime: `W` against the denominator quantum
(`RateModulus.Htel_of_crossdet`), and it is presentation-dependent — the same
ζ(3) is rate-free factorial-cleared and rate-carrying reduced
(`Real213/PresentationDependence`, `zeta3_presentation_overtakes`).  So the
divide algebraic/transcendental, read operationally, is the divide
*form-receipt / race-receipt* — which pocket the distance certificate comes
from.

The number's own degree is then forced into a second-level shape by
`ModulusComposition.powSched_mono`: exponent-cut order transports to schedule
order, so "a degree-τ schedule suffices for this pointing" is monotone in τ —
a cut over exponent cuts.  Its boundary is the classical irrationality
measure; whether that boundary cut is *decidable* is the effectivity question,
and the algebraic case states the gap exactly: the receipt in hand is the
form's `k^s`, the receipt-less truth is exponent 2 — the distance between
them is what non-constructivity costs, measured in degree.

The bridge to the measure is not metaphor: the **cross-determinant is the
best-approximation deficiency**.  `BestApproximation.denominator_lower_bound`
proves that a rational `p/k` strictly between consecutive convergents satisfies
`d_i + d_{i+1} ≤ k·W_i` — to interpose costs denominator `≥ (d_i+d_{i+1})/W_i`.
At the unimodular floor `W_i = 1` (`unimodular_best_approximation`) this is
`k ≥ d_i + d_{i+1}`: the convergents are optimal, the constructive core of the
universal `μ ≥ 2`.  So the residue's shape `W` is the `μ`-content read off the
recurrence with no `limsup` — the boundary cut `μ` is the reached-by-none limit
of this discrete, decidable deficiency.

## Dual function

Stripped of packaging, this is the irrationality-measure hierarchy — Liouville
forms, measure exponents, effective refinements — with one redundancy removed:
the measure was never a property of the number alone, since every certificate
attaches to a presentation.  213's sharpening is to type that fact: degree is
a Lens-output of the pointing (`finite_state_is_of_the_pointing`), the real is
the invariant under rescheduling (`reschedule_limit_eq`), and the "true
degree" survives only as the threshold of a monotone family — a cut, with the
same reached-by-its-pointings status as the real itself.

## Cross-frame connections

The same cover-non-surjection appears at four scales: the stage is of the run
(`theory/essays/foundations/growth_without_a_clock.md`), finite-state is of
the pointing (`theory/essays/synthesis/finite_state_is_of_the_pointing.md`),
completability is of the presentation (`Real213/IntensionalCompletability`),
and now the modulus is of the schedule with the limit invariant
(`reschedule_limit_eq`).  And the grading of *breaks* was already ordinal
(`CompletabilityGrade`'s lex `(height, rate)`); the degree ladder is the
matching grading of *rescues* — between integer exponents the refinement axis
is a log scale, not a power scale, the same ordinal signature.

## Open frontier

The graded rate generator (`Dominates_s` ⟹ `N = k^s`), the conditional
measure-modulus schema (an effective `μ(π)` hypothesis ⟹ a degree-≈7 Wallis
schedule), the two-real separation modulus, tightness of the dyadic exponent
reading, and the degree dynamics (`μ(τ) = τ` self-degree fixed point) are
open, tracked on the frontier board.  The decidability of the degree-threshold
cut for any single transcendental is Roth-grade territory; nothing here claims
it.
