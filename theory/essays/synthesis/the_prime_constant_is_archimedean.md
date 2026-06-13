# The prime number theorem's constant is archimedean

The prime number theorem's constant — the `1` in `π(N)·ln N / N → 1`,
equivalently the `e` in `lcm(1..N) ~ eᴺ` — has no ∅-axiom value because it
is the value of a *single archimedean place*, and every ∅-axiom handle on
prime counting reads the *algebraic* valuation places instead.

## 213-native answer

The logarithm is not one function but a **family of valuations**, one per
place (`theory/essays/analysis/what_is_a_logarithm.md`): the algebraic `vp`
(the prime-exponent count, `vp_mul` sends `×→+`, `vp_pow` sends `^→·`), the
finite-cyclic `ind_g` (the discrete log on `(ℤ/p)*`, valued in `ℤ/(p−1)`,
`theory/essays/synthesis/the_discrete_log_is_the_same_logarithm.md`), and the
archimedean `ln`.  Prime counting is built entirely from the *algebraic*
members; the constant is what is left over once those are weighted by the one
archimedean member.

## Derivation

Everything ∅-axiom-reachable about `π` lives at the algebraic places.  The
central-binomial route's Kummer bound `vp p (C(2n,n)) ≤ ⌊log_p 2n⌋`
(`Lens/Number/Nat213/ChebyshevLower.vp_central_binom_le_floorLog`) is an
inequality between `vp`-readouts; the lcm bridge `C(2n,n) ∣ lcm(1..2n)`
(`central_binom_dvd_lcm`) and the `ψ`-form lower `2^n ≤ lcm(1..2n)`
(`two_pow_le_lcm`) compare `vp` to `vp`.  The structural identity

  `vp p (N!) = Σ_{i=1}^{N} vp p (lcm(1..⌊N/i⌋))`

(`Lib/Math/NumberTheory/FactorialLcmIdentity.vp_factorial_eq_sum_vp_lcm`) is a
*pure* identity at the algebraic place: both sides are `vp`-counts of the same
lattice `{(i,j) : i·pʲ ≤ N}`, read by rows versus columns.  The two homes of
`e` — the factorial (`Σ 1/k!`) and the lcm (`lcm(1..N) ~ eᴺ`) — are one
prime-power skeleton, and the skeleton is entirely algebraic.

The archimedean place enters at exactly one point.  Chebyshev's `ψ` is

  `ψ(N) = ln lcm(1..N) = Σ_{p ≤ N} vp_p(lcm(1..N)) · ln p`,

the algebraic data `vp_p(lcm) = ⌊log_p N⌋` (`vp_lcmUpTo` +
`lcmExpCount_eq_floorLog`) **weighted by `ln p`**.  PNT is `ψ(N) ~ N`, i.e.
the assertion that this single archimedean weighting has slope exactly `1`.
That slope is the constant.  No algebraic identity fixes it: the order theorem
`π(2^{m+1}) = Θ(2^{m+1}/m)` (`chebyshev_order`) traps it in a *computable
interval* `[(m+1)/(2(m+2)), 6]` (`chebyshev_constant_interval`), and sharpening
that interval is genuine ∅-axiom mathematics — but the interval never collapses
to the point, because collapsing it is reading the archimedean place exactly,
which the algebraic skeleton does not determine.

## Dual function

This is the prime number theorem with its packaging stripped: classically the
constant is "where the elementary methods stop and analysis begins," and 213
names *why* the line falls there — it is the `vp`/`ln` = algebraic/archimedean
seam.  The refinement is that 213 keeps the unreachable part **computational**
anyway: the constant is not a transcendent target the bounds approach forever
but a *computed bracket* whose limit is its own name
(`theory/essays/foundations/the_form_of_the_residue.md` "Infinity is the
residue's shape, not a god above it"; `RatTendsToOne` records the two-sided
`→1` pointing shape without an external value).

## Cross-frame connections

The same seam recurs.  `theory/essays/analysis/the_certificate_boundary.md`
draws the certifiability line at hypergeometric (= algebraic = a finite
telescoping witness exists) versus harmonic (= archimedean = explicit-only) —
the Apéry numerator has no clean certificate for the same reason PNT's constant
has no algebraic value.  `what_is_a_logarithm.md` places the divide as `vp`
(algebraic, finite-support) versus `ln` (archimedean).  The discrete-log essay
adds the finite-cyclic end (`ind_g` valued in a finite cycle).  Read together,
the logarithm is *one computed coordinate* whose value-space takes three shapes
— a finite cycle (`ind_g`), a finite-support vector (`vp`), a never-closing
bracket (`ln`) — and the prime number theorem's constant is unreachable
precisely because it is the slope at the only place whose coordinate is the
bracket, not the cycle or the vector.

## Open frontier

The interval is not yet sharp: the base-`2` lower (via the max-binomial
`4^n ≤ (2n+1)·C(2n,n)`) and the base-`≈3.16` upper (unwinding
`LcmGrowthChebyshev`'s 30-block) would trap `e` in a computable `[2, 3.16]`,
and narrowing it further is open ∅-axiom work; the constant `1` itself stays
the asymptotic horizon — a `Real213` pointing (the ratio `π(N)·ln N/N → 1`)
reached by no finite certificate.
