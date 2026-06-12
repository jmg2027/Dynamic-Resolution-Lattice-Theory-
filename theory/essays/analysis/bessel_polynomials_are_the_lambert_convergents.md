# The Lambert convergents are Bessel polynomials

**Question.** The weld glues two pointings of `coth(1/q)` — the Lambert
continued fraction and the Taylor series.  The *series* side is already named
classically in the source (`LambertWeld.lean` §1: the cleared partials
`F_n(u) = Σ_j u^j/((2j)!!·(2n+2j+1)!!)` obey the **Bessel** contiguity ladder
`F_{n−1} = (2n+1)F_n + u·F_{n+1}`, the `I_{ν−1} − I_{ν+1} = (2ν/y)I_ν` relation
at `ν = n+3/2`).  What is the *convergent* side — the coefficient arrays
`apF`/`bpF` that build the CF numerators/denominators `dev q (AP n)` /
`dev q (BP n)`?

**Answer.** They are the **reversed Bessel polynomials** `θ_n`, in the variable
`u = z²`.  The weld is the Padé identity between the two Bessel families — the
denominator family `θ_n` (convergents) and the numerator family `F_n` (series) —
and every quantity the proof leans on is a named feature of those polynomials.

## The recurrence is the Bessel recurrence

`apF`/`bpF` (`LambertMinor.lean:36–50`) are defined by the three-term ladder

```
  apF (n+2) (i+1) = (2n+3)·apF (n+1) (i+1) + apF n i        (head weight 2n+3)
```

Read as the coefficient list of `A_n(u) := Σ_i apF(n,i)·u^i`, this *is*

```
  A_{n+1}(u) = (2n+1)·A_n(u) + u·A_{n−1}(u),     A_0 = A_1 = 1
  B_{n+1}(u) = (2n+1)·B_n(u) + u·B_{n−1}(u),     B_0 = 0, B_1 = 1
```

(the `+ apF n i` at position `i+1` is multiplication by `u`).  This is the
reversed-Bessel recurrence `θ_{n+1} = (2n+1)θ_n + u·θ_{n−1}` — the down-shift
carries `u = z²` rather than `z` because `coth` is **odd**, so its convergents
have definite parity and live naturally in `u = z²`.  `apF`/`bpF` are the
numerator/denominator Bessel polynomials of that family; the partial quotients
`cothCF q n = (2n+1)q` (`ContinuedFractionModulus.lean:262`) are the odd stream
`(2n+1)` that the ladder threads.

## The named features, term by term

The first arrays (`#eval`-verified):

```
  apF:  A_2 = 3 + u    A_3 = 15 + 6u    A_4 = 105 + 45u + u²    A_5 = 945 + 420u + 15u²
  bpF:  B_2 = 3        B_3 = 15 + u     B_4 = 105 + 10u         B_5 = 945 + 105u + u²
```

- **Constant term = `θ_n(0)` = the odd double factorial.**
  `apF n 0 = bpF n 0 = (2n−1)!!`  (`1,1,3,15,105,945,10395,…`).  Both families
  share their bottom coefficient — the value of the Bessel polynomial at the
  origin — and it is exactly the product of odds `1·3·5···(2n−1)`, the leading
  coefficient of the *un*reversed Bessel polynomial `y_n`.

- **First coefficient = `(n−1)·(2n−3)!!`** for `apF` (`0,0,1,6,45,420`), the
  next reversed-Bessel coefficient.

- **Leading coefficient = the Padé flip `cfpos`.**  At matched depth the top
  surviving coefficient is `cfpos(2i+1, 2i+1) = 2^{2i+1}·descFac(2i+1, 2i+1) =
  2^{2i+1}(2i+1)! = (4i+2)!!` (`LambertMasterId.lean:323,470`).  This is the
  classical diagonal-Padé remainder leading coefficient `2^n n!` of the
  reversed Bessel `θ_n` — the integer-cleared form of the analytic remainder's
  `1/[(2n−1)!!(2n+1)!!]`.

- **Total positivity = Bessel total positivity.**  `minor_all`
  (`LambertMinor.lean:343`): `apF n i · bpF n j ≤ bpF n i · apF n j` for `i < j`
  — the convergent coefficient matrix is totally positive.  This is precisely
  the known total positivity of Bessel-polynomial coefficient matrices (the
  Hankel/Turán inequalities for Bessel polynomials); the weld's monotone
  machinery (`weight_dom`, `cross_le`) re-derives it subtraction-free.

## The weld is the two Bessel families meeting

The master identity `Asum(2k+1,N) + cfpos(2k+1,N) = Bsum(2k+1,N)`
(`master_odd`, `LambertMasterId.lean:457`) is the **Padé matching** of the
denominator family `θ_n` against the numerator family `F_n`: the first `2i`
coefficients cancel (the `u^{2i}`-order Padé condition, `descFac_vanish`), and
the first surviving difference is `(4i+2)!!`.  `LowerBase` (the base inequality
the weld needs) is the statement that this flip is non-negative and dominates
the sub-diagonal slack (`bpF_le_cfpos`: `2i·(4i+1)!! ≤ (4i+4)·(4i+2)!!`).  So:

> the **series** pointing is `F_n` (Bessel numerator ladder), the **convergent**
> pointing is `θ_n = apF/bpF` (Bessel denominator polynomials), and their
> agreement (`weld_closed`) is the classical fact that the diagonal Padé
> approximant of `coth` *is* its truncated series — both governed by the one
> Bessel three-term recurrence and meeting at the double-factorial flip.

## What is 213-native

The mathematics is classical (Lambert 1761; Hermite; the Bessel/Padé theory of
`coth`/`e^z`; Bessel-polynomial total positivity).  What the residue rebuild
adds is *form*: the entire Bessel/Padé structure is re-encoded as finite,
subtraction-free ℕ-combinatorics with **zero axioms** — Hermite's *integral*
remainder replaced by the arithmetic `cfpos_moved` recurrence; the Bessel
contiguity replaced by the coefficient ladder; total positivity by `cross_le`.
And the Casoratian organizing it — the weighted cross `K_J` with the det-one
floor `+1` as a residue unit (`when_two_pointings_are_one.md`,
`weld_casoratian_development.md`'s bilinear unification) — names a structure the
scattered classical computations leave implicit: the two Bessel families are one
unimodular `(ĉ, s)` pair, and *every* residual cross is `det(coeff)·K_J`.

**Constructive object.**  `apF`/`bpF` (`LambertMinor.lean`) — the reversed
Bessel polynomials of `coth`, as `∅`-axiom ℕ coefficient functions; their
matched-depth leading coefficient `cfpos = 2^n·descFac` is the double-factorial
Padé flip the weld is built on.
