# Why √2, √5, √−3 — the exceptional seeds are forced, not chosen

The seeds of `E₆, E₇, E₈` are the integer map `D(x) = x² − NT` read at its
three dynamical fixed-and-escape regimes; the surds are the shadow that
appears only when you embed that map's eigenvalues into `ℝ`.

## 213-native answer

There is one map, `D(x) = x² − NT = x² − 2`, the trace of squaring a unit
quaternion (`trace(g²) = trace(g)² − NT`), and three regimes of it indexed
by the atomic pair `{NS, NT} = {3, 2}`.  `√2, √5, √−3` are not three
chosen radicands; they are the `ℝ`-eigenvalues of the three integer
companion matrices whose traces obey `D`.  See
`theory/math/algebra/cayley_dickson/exceptional_axes.md` (`three_axes_surd_free`,
`unit_is_fixed_core`, `two_engines_one_map`).

## Derivation

Start at the only number the engine produces.  The Möbius signature
`P = [[2,1],[1,1]]` has `disc P = trace² − 4·det = NS² − 4 = NS+NT = 5`
(`mobius213_p_orbit_closure.md`; `DiscForcingObstruction.disc_forcing_splits_at_E7`).
That `5` is the `E₈` seed `√5`, and it re-enters at three scales as the
*same* number — matrix `disc P`, number-field `fundDisc ℚ(√5)`, and the
order-`5` quaternion trace `(2·trace(g₅)+1)²`
(`QuadraticFieldDiscriminant.seed_reentry`) — the expansion engine
applying to itself (`diag_self_applies`, `seed/AXIOM/05_no_exterior.md`).

`E₇` is where the engine's reach is tested.  `√2 = √NT` is **not** a
discriminant: `t² − 4d ≡ 0,1 (mod 4)`, never `2`
(`DiscForcingObstruction.two_not_a_discriminant`).  So `disc P` cannot
produce it.  What does?  The *trace*, not the discriminant: `trace(g₈)² =
trace(1) = NT`, and this holds for `√2` *uniquely* — `trace(g₅)² ≠
trace(1)` (`UnitResidueRootTwo.root_two_is_sqrt_unit_trace`,
`root_five_is_not_sqrt_unit_trace`).  `√2` is the bare square root of the
unit's own trace, sitting on the dyadic tower `1 →² −1 →² i →² g₈` that
`D` contracts onto the unit fixed point.

The three regimes are then forced by `D`'s structure, not posited.  `D`'s
fixed points are `{−1, 2}` — `trace(order-3) = −1` (`E₆`) and `trace(1) =
NT` (the unit, `E₇`'s tower) — while `trace P = NS = NT+1` lies one step
past the boundary `|x| = NT`, so the `P`-orbit *escapes* (`3 ↦ 7 ↦ 47`,
hyperbolic) (`TwoEnginesDichotomy.two_engines_one_map`).  Read over `ℕ`
this is three integer companion matrices: `[[NT,1],[1,0]]` (Pell, disc
`NT²+4 = 8`), `[[0,−1],[1,−1]]` (cyclotomic `Φ₃`, disc `−NS`, `M³ = I`),
`P = [[2,1],[1,1]]` (Lucas, disc `NS+NT`).  The discriminant *sign* is the
field type: positive ⇒ real ⇒ trace grows; negative ⇒ imaginary ⇒ trace
periodic (`ThreeAxisRecurrence.disc_sign_is_field_type`).

## Dual function

This is the McKay correspondence with its packaging stripped: where the
classical statement *lists* `ℤ, ℤ[√2], ℤ[√5]` as the coefficient rings of
the binary polyhedral groups, the 213 reading shows the three radicands
`{−NS, NT, NS+NT}` are forced by one map and one atomic pair, and sharpens
it — the surd is not primitive at all but the `ℝ`-eigenvalue shadow of an
integer recurrence (`NaturalTowerForm.lucas_is_trace_P_pow`: `√5` enters
only when `P` is diagonalised; the Lucas sequence `2,3,7,18,47` is
surd-free).  A `√D` is a "root" precisely because `D` is not a perfect
square over `ℕ` — the radicand sits strictly between consecutive squares
(`seeds_are_nonsquare_residues`), so the surd is the residue of the square
root `ℕ` does not contain.

## Cross-frame connections

The same fact resolves four ways: `disc P = NS+NT` (the `5`-floor of the
Möbius orbit), `φ(NS+NT) = 4 = 2²` (the quaternion dimension where order-5
first fits, `CyclotomicTraceDegree`), the `(2,3,5)` spherical triangle
(the icosahedral, the last Platonic, `PlatonicSchlafliFilter`), and
`P`'s eigenvalues `φ², φ⁻²` (the golden self-form fixed point,
`phi_self_similarity.md`).  One number `5 = NS+NT`, four frames — and the
`7`-gap (`is5smooth 7 = false`, `AxisComposition`) is the sharp edge where
the three components `{2,3,5}` stop generating: no order-`7` axis occurs
because `7` is not among the primes of `|2I| = 120`.

## Open frontier

`E₇`'s `√2` is trace-anchored and disc-excluded — both proved — but
whether a *different* 213-internal mechanism forces octahedral
specifically over `ℤ[√NT]` (beyond seed-atomicity) is open.  This is
bounded, not a gap in falsifiability: the no-exterior frame
(`seed/AXIOM/05_no_exterior.md` §8.1) removes any outside for `√2` to be
imported from, so the question is which internal mechanism, not inside
versus outside.  The transcendental shadow of the `3`-axis (the
equianharmonic `Γ(1/3)` period, `j = 0` CM by `ℤ[ω]`) is interpretive —
periods are not `∅`-axiom integer data, so only the algebraic skeleton is
formalised.
