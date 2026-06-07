# Quadratic reciprocity

For distinct odd primes `p, q` (`m = (p−1)/2`, `n = (q−1)/2`): the question "is `q` a square
mod `p`?" and the mirror "is `p` a square mod `q`?" give the same answer exactly when the count
`m·n` is even. The law is not a statement about a symbol `(q/p)`; it is a count-equality between
two halves of a lattice rectangle.

## 213-native answer

"`q` is a quadratic residue mod `p`" is a count-Lens reading (`seed/AXIOM/06_lens_readings.md`
§6.7): the residue class `q % p` — the count-Lens applied through the difference-Lens readout that
*is* `ℤ/p` — either lies in the image of the squaring map `z ↦ z² % p` on `[1,p)` or it does not.
There is no Legendre-symbol primitive; `quadratic_reciprocity`
(`lean/E213/Lib/Math/NumberTheory/ModArith/QuadraticReciprocity.lean`) states the bare
biconditional

```
(∃z, z² ≡ q mod p) ↔ (∃z, z² ≡ p mod q)   ⟺   (m·n) % 2 = 0.
```

No modulus is privileged: `p` and `q` are two count-Lens moduli (`leavesModNat`,
`theory/math/numbertheory/modular_arithmetic.md`), and reciprocity says the two readings agree,
gated by one parity bit.

## Derivation

The closure runs entirely through counting — the residue's count-Lens reading pointing at itself —
which is why it needs no exterior.

First, `floor_qr` collapses "is `q` a square mod `p`?" to the parity of a *count*: via Euler's
criterion (`euler_criterion`, `EulerConverse.lean`) and Gauss's lemma (`gauss_qr`, `GaussLemma.lean`;
μ-form `gauss_mu`), `q` is a residue iff `μ` is even, and the Eisenstein refinement `gauss_mu_gen`
shows `μ ≡ Σ_{x=1}^{m} ⌊q·x/p⌋ (mod 2)`. The floor `⌊q·x/p⌋` is itself a count: by
`colCount_eq_floor`, it equals `#{ y ∈ [1,n] : p·y < q·x }` — the lattice points in column `x` below
the diagonal `q·x = p·y`.

Second, `floor_sum_rectangle` is the heart, and it is a literal application of the count-Lens to a
rectangle. The grid `[1,m] × [1,n]` has `m·n` points (`count_all` squared). Each point falls
strictly on one side of the diagonal `q·x = p·y` — never on it, because `p ∤ q·x` for `x ∈ [1,m]`
(`not_dvd_seg` + prime Euclid `nat_prime_dvd_mul`). So the trichotomy `elem_tri`
(`[py<qx] + [qx<py] = 1`) partitions the grid with nothing on the boundary, and a finite Fubini swap
(`sumZ_swap`) gives

```
Σ_{x=1}^{m} ⌊q·x/p⌋  +  Σ_{y=1}^{n} ⌊p·y/q⌋  =  m·n.
```

Third, `parity_sum_iff` reads the answer off the sum: two integers `S, T` with `S + T = m·n` have
`2∣S ↔ 2∣T` precisely when `m·n` is even. The two squaring-readings agree iff the two counts share
parity iff their sum `m·n` is even. That is the law.

## Dual function

Classically this is the deepest elementary theorem in number theory, dressed in Legendre symbols and
`(−1)^{mn}`. Strip the packaging (`seed/AXIOM/05_no_exterior.md` §0): there is no `(q/p)` object and
no formal sign — `m·n` is the actual cardinality of the rectangle `[1,m]×[1,n]`, and the exponent's
parity is the count-Lens readout of that cardinality. The 213 reading is sharper exactly here: the
sign `(−1)^{((p−1)/2)((q−1)/2)}` is the number of lattice points in a box, mod 2.

## Cross-frame connection

The step that makes the count clean is that no integer point lies on the exact diagonal
`q·x = p·y` — the residue never reaches it (`p ∤ q·x`). This is the same shape as
`object1_not_surjective` (`seed/AXIOM/05_no_exterior.md` §8.1): the boundary value is reached by none
of the readings, so the count splits exhaustively into two sides with no remainder. The diagonal is a
Lens-artifact (a floor/boundary, `seed/AXIOM/06_lens_readings.md` §6.9), not an inhabited point — the
same fact that lets `parity_sum_iff` treat `S + T` as a clean two-way split with no third term.

## Open frontier

This is closed strict ∅-axiom for the quadratic character. The cubic and biquadratic reciprocity
laws — the same count-Lens question over `ℤ[ω]` and `ℤ[i]`
(`theory/math/numbertheory/eisenstein_period_arithmetic.md`) — are the natural continuation and are
not yet 213-native; the analytic / Gauss-sum proofs of quadratic reciprocity are likewise not (and
need not be) reproduced, since the lattice count already closes it.
