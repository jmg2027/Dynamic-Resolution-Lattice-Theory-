# What is `×`?

`×` is `+` with distinguishable atoms: the second rung, `+` iterated,
whose value-object is a grid, and which is `+` *itself* run on the
prime-exponent lattice.  The sole content separating `×` from `+` is that
`×`'s atoms (primes) are distinguishable where `+`'s atoms (units) are not.

## 213-native answer

`×` is `+` iterated: `a · b = iter (· + a) b 0` (`Iterate213.mul_eq_iter`)
— `b` copies of `a`, summed.  Its value-object is the `a × b` grid of
units, count `a · b` (`UnitGrid.total_rows`).  The increment `a` and the
counter `b` are *both lengths* — the same type — which is exactly why `×`,
unlike `^`, stays commutative.

## Derivation

Commutativity is born from the grid transpose.  The grid's two axes are
both unit-lengths, so transposing rows and columns is a symmetry; counting
forgets which axis is which, and `a · b = b · a`
(`UnitGrid.mul_comm_from_grid`) — the level-2 sibling of `+`'s
`append_comm` (`theory/math/numbersystems/slot_arithmetic.md` §1.5).

`×` is `+` on the exponent lattice.  For each prime `p`, multiplication
*adds* the exponents: `vp p (m · n) = vp p m + vp p n`
(`Meta/Nat/VpMul.vp_mul`).  So `×` is not a new operation — it is `+`
itself, run independently on each prime axis.  The exponent vector
`exp(n) = (vp 2 n, vp 3 n, …)` is the **×-count-Lens** (the ×-analog of
`count`), a *vector* because `×`-atoms are distinguishable where `+`-atoms
are not (`seed/AXIOM/06_lens_readings.md` §6.7; the atom-(in)distinguishability
handle).  This is the whole difference between `+` and `×`.

`×` *is* the divisibility order.  Its witness question `a · x = b` founds
`∣` (`a ∣ b ↔ ∃x, a · x = b`), parallel to `+`'s witness `a + x = b`
founding `≤`; the obstruction readout is the remainder, located by the
÷-sandwich (`Meta/Nat/NatDiv213.div_sandwich`), and the inverse question
mints ℚ (`Lens/Number/RatioLensFounding.ratioEquiv`).

`×` is a factorization.  `a · b` is the product-collapse of the 2-factor
shape `(a, b)` (`Meta/Nat/Shape213.shapeProduct`); the grid shape *is* a
factorization, and the prime `exp` is the maximal-dimension one
(`Shape213.refine_*`).  So the substrate dimension of `×` (a 2-grid) and
the atom-coloring (`exp`) are one structure at different resolutions, not
two.

## Dual function

Classical "multiplication = repeated addition" (Euclid) *is*
`mul_eq_iter`; 213 sharpens that `×` is the *same* operation as `+` one
resolution up — `vp_mul` makes `×` literally `+` on the exponent lattice
— and `×`-commutativity is the grid transpose, a theorem, not an axiom.
The "units" of that upper `+` are the distinguishable primes; their
distinguishability is the entire content that promotes `+` to `×`.

## Cross-frame connections

Five readings, one operation: iterate `+` (`mul_eq_iter`), grid count
(transpose-commutative, `mul_comm_from_grid`), `+` on exponents
(`vp_mul`), the `∣`-order witness (`a · x = b`), the 2-factor
factorization (`Shape213`).  They converge — repeated addition *is* the
grid count *is* addition-on-exponents *is* how-many-times-divides *is* a
factorization.  The same convergence `+` has, one rung up, with the unit
replaced by the prime.

## Open frontier

`vp_separation` — `(∀ p prime, vp p m = vp p n) → m = n` (unique
factorization) — is **open**.  It is what *licenses* `exp` as a faithful
coordinate, i.e. "`×` = the free commutative monoid on the primes".  So
"`×` is `+` on the exponent lattice" is multiplicativity-*proved*
(`vp_mul`) but faithfulness-*open*: the additive structure of the upper
rung is established; that its axes are genuinely independent (the primes
free) is the remaining brick.
