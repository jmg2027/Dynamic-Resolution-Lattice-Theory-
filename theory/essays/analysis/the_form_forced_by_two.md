# The weld's form is forced by two

The Lambert weld's entire shape — one Casoratian `K`, every residual cross a
multiple of it, a unimodular transform, a det-floor unit, a double-factorial
flip — is forced by a single fact: the solution space is **exactly
two-dimensional**.  Nothing chooses the form; "two" forces all of it.

## 213-native answer

`coth(z) = cosh(z)/sinh(z)` is the ratio of the two solutions of one
second-order linear system (`y'' = y`).  Two solutions = a rank-2 space.  A
rank-2 space carries a **unique** (up to scalar) alternating bilinear
functional — its Casoratian.  Every quantity the weld builds lives in that one
space, so every cross-determinant it forms *must* be that one functional times
a constant.  The form is not designed; it is what two-dimensionality permits,
and two-dimensionality permits nothing else.

## Derivation

The weld's pieces are all combinations of one normalized pair `(ĉ, s)`, `ĉ_J =
(2J+1)·c_J` (`theory/math/analysis/lambert_weld.md` §9; `weldR_basis`,
`weldM_basis`, `weldK_basis`).  Its Casoratian is `K_J = ĉ_{J+1}s_J − ĉ_J
s_{J+1}`.  The lower cross and upper margin are *constant*-coefficient images
of this pair: `R = devB·ĉ − devA·s`, `M = −q²Q·ĉ + P·s`.

That one structural fact dictates the rest, each forced, none chosen:

- **All crosses collapse to `K`.**  `weld_bilinear_casoratian` (a pure ℤ ring
  identity, `lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/LambertOrder.lean`):
  for `X = a₁ĉ+a₂s`, `Y = b₁ĉ+b₂s`, the cross `X_{J+1}Y_J − X_J Y_{J+1} =
  (a₁b₂−a₂b₁)·K_J`.  There is no second invariant a 2-D space could offer; the
  alternating form is one-dimensional.  So `R×s`, `M×s`, `M×ĉ`, `R×M` are all
  `det(coeff)·K` — the "three Wronskians" are one identity read four ways.

- **The transform is unimodular.**  `(s, ĉ)` is the image of `(R, M)` under the
  CF-determinant matrix; its determinant is `q²Q·devA − P·devB = −1`
  (`dev_cross_det`, `weld_cosh_RM`).  This `±1` is not a tuned constant — it is
  the determinant of a single continued-fraction step `[[a_n,1],[1,0]]`, forced
  to a unit because each CF step is an elementary `SL(2,ℤ)` move.

- **The `+1` is the residue unit.**  Because the transform is unimodular, the
  fundamental cross `R_{J+1}M_J − R_J M_{J+1}` is exactly `K_J` with coupling
  `1`, no lower-order correction (`weld_casoratian_bilinear`).  The det-floor
  `P·devB − q²·devA·Q = 1` is the one quantity the alternating form cannot
  reduce away: the unit a determinant returns on a basis.

- **The flip is the accumulated determinant.**  Telescoping the recurrence
  weights `(2J+1)(2J+2)` of the cleared cosh/sinh partials gives the matched-depth
  leading coefficient `cfpos(2i+1,2i+1) = 2^{2i+1}(2i+1)! = (4i+2)!!`
  (`master_diagonal`) — the double factorial is the Casoratian accumulated over
  `2i+1` steps, the Padé remainder of the same rank-2 system
  (`theory/essays/analysis/bessel_polynomials_are_the_lambert_convergents.md`).

## Dual function

This is the classical Bessel/Padé theory of `coth` — convergent denominators
are Bessel polynomials, the remainder a double factorial, the convergent matrix
unimodular (Lambert; Hermite; Padé) — with the packaging that makes those facts
look separate stripped: they are one consequence of rank 2, and 213's reading
names the organizing object the scattered classical computations leave
implicit — the unit-`K` collapse and the det-floor `+1` as a residue unit, not a
coincidence of formulas.

## Cross-frame connections

"Two" here is the count-Lens reading of the first distinguishing
(`seed/AXIOM/06_lens_readings.md`; CLAUDE.md *Count-Lens import as Raw*): `coth`
is "the ratio of two distinguishables," and the rank-2 structure is that count
made into a solution space.  No exterior dialer sets the shape
(`seed/AXIOM/05_no_exterior.md` §5.1) — the unimodular `+1`, the odd partial
quotients `(2J+1)q`, the double factorial are all forced downward from "two,"
the way the alternating-form/symmetric-product split is forced on any rank-2
floor (the weld's Casoratian and `Convolution213`'s `conv` are the two halves —
`weld_crossdomain.md` addendum).  Rank 1 would be rational (no transcendental
ratio); rank 3+ would admit more than one invariant.  Two is the unique floor
on which a transcendental ratio has *exactly one* alternating certificate — so
the weld has exactly the shape it has.

## Open frontier

That the form is forced does not make every consequence free: `LowerBase`'s
matched-depth flip value (`(4i+2)!!` dominating the sub-diagonal slack) is still
a genuine quantitative count, and a bridge-free induction for the margin's
monotonicity is open (`transcendentals/weld_casoratian_development` frontier).
Two-dimensionality fixes the *shape*; the *size* of the flip is the work the
bridge does.
