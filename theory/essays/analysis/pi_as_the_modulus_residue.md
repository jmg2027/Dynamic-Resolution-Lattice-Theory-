# π as the modulus-residue — what every finite modulus leaves

π read through the modulus family: every lattice modulus realizes a finite
period, and what the whole family fails to realize — uniformly, provably — is
the rotation whose period is π.  The reading characterizes; the cut
constructs; the gap between them is one named inequality.

## 213-native answer

The ∀-form reading of π is the residue form instantiated at the modulus-Lens
family.  The residue is outside every view's image
(`Lib/Math/Foundations/ResidueForm.object1_not_surjective`;
`seed/AXIOM/05_no_exterior.md` §5.1: pointings converge, none reaches), and
the modulus family makes this quantitative in two registers, both ∅-axiom:

**The finite side is a closed spectrum.**  Every integer rotation of finite
order has order in `{1, 2, 3, 4, 6}` — for every `M ∈ SL(2,ℤ)` and every
exponent, `M^{n+1} = I` forces `M¹² = I`
(`Real213/FiniteOrderSpectrum.finite_order_spectrum`,
`finite_order_divides_twelve`), orders 4 and 6 realized exactly by the
Gaussian and Eisenstein generators (`exact_order_four`, `exact_order_six`),
order 5 forbidden (`no_order_five` — no five-fold lattice symmetry; the
pentagon axis is the golden, not the modular, direction:
`PentagonGoldenTrace`).  Six is the last finite period
(`theory/essays/analysis/the_modular_group_from_two_folds.md`).  The
remainders the family leaves, `2 − 2cos(2π/k) = 4sin²(π/k) ≈ 4π²/k²`, spell
π in their decay constant: the family does not merely miss the full rotation,
it encodes what it misses.

**The escape side is priced, not free.**  Reading the cut of π through its
Wallis pointing, the race against the probe quantum is lost at *every* grade:
the cross-determinant is the full product `W_n = a_n·d_n`
(`ExpLog/PiMeasureModulus.wallis_cross_det`), so scheduled domination fails
for every positive schedule at every layer ≥ 2
(`wallis_overtakes_every_schedule`, `wallis_no_graded_certificate`) — the
pointing sits beyond every rung of the graded ladder
(`theory/math/analysis/holonomic_modulus.md` §4).  What converts the ∀-form
into a *constructor* is its quantification: "modulus `k` leaves at least
`1/(C·k^s)`" is an effective irrationality measure, and given that one
inequality (`PiHalfMeasure C s`) the cut completes with the constructed total
modulus `N(m,k) = C·(2k)^s + 2` (`pi_measure_modulus`).  Bare universal
escape characterizes; escape **with a witness function** defines.  The only
fully explicit classical instance is Mahler's 1953 measure
`|π − p/q| ≥ q⁻⁴²` (all `q ≥ 2`, constant 1); the sharper records
(Salikhov 2008, Zeilberger–Zudilin 2020, exponent ≈ 7.1) are effective in
principle with unpublished constants.

## Derivation

The two registers are one comparison read at its two ends.  The spectrum
theorem says the modular family's periods close at 12; the rotation
interpolating the elliptic generators does not belong to the family — its
trace datum at modulus `k`, `2cos(2π/k)`, is realized and algebraic at every
`k`, while the limit of the family is the trace floor 2, not π.  The escape
theorems say the same from the cut side: no schedule of finite polynomial
slack absorbs the Wallis pointing's overtake, exactly as no finite-order
element realizes the full period.  Between them sits the structural fact that
the ∀-form cannot do the constructing alone: the algebraic circle
`{(c,s) : c² + s² = 1}` is π-free but carries no speed, so "the rotation"
underdetermines its period until a pointing (a series fold with its own
modulus, e.g. the `y″ = −y` route of
`theory/math/analysis/holonomic_modulus.md`) anchors it.  The moduli
determine the metric of their own leftover; the completion — the number — is
the cut machinery's step (`theory/math/numbersystems/real213.md`), and the
machinery's price list is explicit: free for rate-carrying pointings,
`C·k^s + 2` conditional on the measure for π.

## Dual function

The classical concept recovered with its packaging stripped is the
**irrationality measure**: stated 213-natively it is nothing but the
quantified ∀-form — a per-modulus escape floor — and the engine that consumes
it (`BracketModulus.bracket_total_modulus`) shows the measure was never a
property *about* π so much as the missing component *of* π's decision
procedure.  The refinement runs the other way: 213 types exactly where the
number enters (the cut constructor, not the modulus family, not the forced
character of the adelic register) and prices what each pointing lacks — the
rung is a Lens-grading of pointings (`PresentationDependence`,
`depth_is_intensional`), the residue sits in no rung, and π's apparent
specialness is an **effectivity gap** (explicit exponent 42 against the
conjectured 2), not Diophantine exoticism: conjecturally `μ(π) = 2`, the
generic value.

## Cross-frame connections

Four resolutions of one non-enclosure: the residue outside every view
(`object1_not_surjective`); every lattice period dividing 12
(`crystallographic_spectrum`); every schedule overtaken
(`wallis_no_graded_certificate`); every presentation's rate belonging to the
pointing while the cut is invariant (`rcut_rescale`,
`crossDetSmall_is_presentation_dependent`).  The first is the axiom-scale
form; the other three are its modulus-scale shadows — finite-order, race, and
gauge readings of "reached by none."

## Open frontier

An actual effective `(C, s)` instance for `PiHalfMeasure` — Mahler-42 is the
named classical target whose formalization (exp/log Hermite–Padé) would turn
the conditional modulus unconditional.  The quantitative bridge between the
spectrum register and the escape register (discrepancy of the rotation orbit
against finite character sums; the orbit's gap structure is π's continued
fraction) is recorded as a long-range direction; the continued-fraction
non-holonomicity of π remains the standing classical open problem behind it.
