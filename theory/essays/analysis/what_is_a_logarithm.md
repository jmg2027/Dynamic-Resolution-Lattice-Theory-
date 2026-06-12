# What is a logarithm (in 213)?

A logarithm is the **demotion coordinate**: the readout in which a tower rung
becomes the rung below it — `×` read as `+`, `^` read as scalar `·`.  Its
arithmetic realization is `vp`, the prime-exponent valuation; the pair
*(operation, its demotion)* is the logarithm, with no analytic function imported.

## 213-native answer

`vp p n` — the largest `k` with `pᵏ ∣ n` (`Meta/Nat/Valuation.lean`) — *is* the
logarithm, read one prime at a time.  Two equations carry it:

- `vp_mul` : `vp p (m·n) = vp p m + vp p n` — the log of a product is the sum
  (`×` demoted to `+`).
- `vp_pow` : `vp p (aᵏ) = k · vp p a` — the log of a power is the scalar multiple
  (`^` demoted to scalar `·`).

(`Meta/Nat/VpMul.lean`.)  So the logarithm is not a primitive analytic function;
it is the **count-Lens on the multiplicative atoms** — a number's multiplicative
content is its factor list (`theory/math/numbersystems/slot_arithmetic.md` §1.5;
`Meta/Nat/Shape213.lean`), and `vp` counts how many times each prime atom appears.
Counting the atoms turns multiplying into adding.

## Derivation

The tower `+ → × → ^` is one generator iterated (`HyperLadder.hyperop_succ`):
each rung is the previous, counted.  The logarithm runs the **other direction** —
it *unbuilds* a rung to the one below.  In the prime-exponent lattice this is
exact and discrete: `×` is vector addition on the prime axes (`vp_mul`), `^` is
scalar multiplication of the whole vector (`vp_pow`), so `vp` lays the
multiplicative tower flat onto the additive one (`ExpVector.{toVec_mul,
toVec_pow}`).  The tower is thereby **one operation (addition) seen at successive
log-depths**.

This logarithm is *faithful*: the readout determines the number
(`VpSeparation.vp_separation`, unique factorization — `exp` is injective), and it
is *finite-support* — `vp p n = 0` for every prime `p > n`
(`FoldCriterion.vp_eq_zero_of_gt`), so each number's log is a finite list of
prime-coordinates.  Solving `aˣ = b` becomes the question *"is `vp b` a scalar
multiple of `vp a`?"* — solvable exactly when the exponent-vectors are collinear
(`FoldCriterion.fold_iff_collinear`); distinct primes are independent axes
(`prime_pow_unique`), so `2ˣ = 3` has no answer in the lattice and the logarithm
there is a non-folding cut (`Lib/Math/NumberSystems/Real213/…`), not a lattice
point.

A valuation is what `vp` *is*: the defining laws are `v(a·b)=v(a)+v(b)` (the log)
and `v(0)=∞`.  That `vp` sends `0` to `∞` is the residue identity `0 ≡ ∞`
(`seed/AXIOM/06_lens_readings.md` §6.5/§6.9) read arithmetically — the logarithm
is the readout that gives `∞`/`0` a finite coordinate elsewhere (every nonzero
`n` gets a finite exponent), which is why it is the level's *invariant*.

## Dual function

The analytic `ln`, with its packaging stripped — the real/complex function, the
branch cut, the transcendence — *is* this valuation: the exponent-readout that
sends products to sums.  213's sharper reading is that the logarithm is **one
choice of place**: `vp` is the logarithm at the prime `p` (algebraic, faithful,
finite), and the familiar `ln |·|` is the logarithm at the *archimedean* place
(the size).  The product formula ties the places; the archimedean log is the one
that carries transcendence (`ln 2, ln 3, …` ℚ-independent), while each `vp` stays
arithmetic.  "The logarithm" is not one transcendental function but the family of
valuations, the count-Lens read at each place.

## Cross-frame connections

The logarithm appears as **one object in three readouts**: the **demotion**
(`× → +`, `^ → ×`), the **valuation/invariant** (`vp`, the gauge-invariant of the
level), and the **inverse of `exp`** (where `exp` is iterated `×`).  Up the tower
it is `vp` at `×`, the archimedean cut at `^`, and the **super-logarithm** (the
Abel function `α`, `α(a^z)=α(z)+1`) at `↑↑` — the same demotion, three places.
And it is the same fact as faithfulness: `vp_separation` (the log determines the
number) is exactly "the demotion loses nothing through `^`."

## Open frontier

Through `^` the demotion coordinate is canonical (the ordinary log is unique).
At `↑↑` the super-logarithm exists but is **holonomic** — non-unique up to a
1-periodic function, non-elementary (Kneser) — so the logarithm there is a gauge,
not a function (the value it would return is presentation-dependent).  The
valuation that would survive that gauge — a growth-*rank* logarithm for the
iteration level, the `vp` of the fast-growing hierarchy — is standard Hardy-field
material, not yet built ∅-axiom.
