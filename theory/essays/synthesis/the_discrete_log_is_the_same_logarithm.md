# The discrete logarithm is the same logarithm

The discrete logarithm `ind_g a` — the position of a unit `a` in the single
orbit `g⁰,…,g^{p−2}` of `(ℤ/p)*` — is the additive coordinate of a cyclic
generator, the same object `vp` is one prime at a time.  The quadratic character
`(a/p)` is that coordinate read at resolution 2: its lowest digit.

## 213-native answer

A logarithm is the **demotion coordinate** of a cyclic structure — the readout
in which `×` becomes `+` (`theory/essays/analysis/what_is_a_logarithm.md`).  Fix
a generator; every element is one of its powers, and the logarithm returns the
exponent.  `vp p n` does this for the infinite cyclic `⟨p⟩ ≅ ℤ` —
`vp_mul : vp p (m·n) = vp p m + vp p n` (`Meta/Nat/VpMul.lean`).  The **discrete
logarithm** does the identical thing for the *finite* cyclic `(ℤ/p)*`: a
primitive root `g` exists (`theory/math/numbertheory/primitive_roots.md`,
`exists_primitive_root`), its powers list every unit exactly once, and
`ind_g (a·b) = ind_g a + ind_g b` valued in `ℤ/(p−1)`.  Same equation, finite
ring of exponents.

The two differ only in the atom set.  `vp` reads a number against **many**
independent prime axes (`prime_pow_unique`); `(ℤ/p)*` carries a **single** atom —
the generator `g` — so its logarithm is one coordinate, valued in `ℤ/(p−1)`
instead of `ℤ`.  The archimedean `ln |·|` is the same demotion at the
size-place.  Three instances — one per prime, one per `(ℤ/p)*`, one
archimedean — of a single object: the additive coordinate of a cyclic generator
(`what_is_a_logarithm.md`, dual function).

## Derivation

The quadratic character is then forced, not stapled on.  `(ℤ/p)*` has even order
`p−1 = 2m`; its unique order-2 element is `−1`, and the generator's halfway power
`g^m` must be it (`theory/essays/synthesis/the_quadratic_character_is_a_discrete_log_parity.md`).
So for `a = g^k`,

```
(a/p) = (−1)^k = (−1)^{ind_g a},
```

the **count-Lens at resolution 2** (`seed/AXIOM/06_lens_readings.md`) reading the
orbit-position counter — the lowest digit of the discrete logarithm.  A square is
an even coordinate, a non-residue an odd one.  Euler's criterion
`a^m ≡ (−1)^k` is the same statement read the other way: raising to the
half-order projects the coordinate onto its top bit
(`theory/math/numbertheory/legendre_symbol.md`,
`theory/math/numbertheory/quadratic_reciprocity.md`).

## Dual function

The classical "index" / "discrete logarithm," packaging stripped, *is* a
logarithm — the cyclic coordinate, finite case — and the Legendre symbol,
packaging stripped, *is* its lowest digit.  213's sharper reading: "character" is
not a predicate fixed to the units from outside but the count-Lens reading the
orbit at a coarse resolution; reading at any resolution `d ∣ (p−1)` gives the
order-`d` power-residue character by the same move.  The quadratic one is `d = 2`
— the parity.

## Cross-frame connections

One fact in four frames: the **discrete log** `(a/p) = (−1)^{ind}`; the
**valuation parity** (the lowest digit of `vp`, the demotion's resolution-2
readout — `what_is_a_logarithm.md`); the **permutation sign** of
multiplication-by-`a` (a single `(p−1)`-cycle raised to the `k`,
`ZolotarevCycle.zolotarev_full`,
`theory/essays/synthesis/the_permutation_under_three_readouts.md`); and the
**sign of a pointing** (`theory/essays/synthesis/the_legendre_symbol_is_the_sign_of_a_pointing.md`).
One coordinate, read at resolution 2, named four ways — character, parity, sign,
Legendre symbol.  The "logarithm = cyclic coordinate" reading is what fuses them:
each is the lowest digit of *the same* exponent.

## Open frontier

Whether the order-`d` characters for the other `d ∣ (p−1)` (the full count-Lens
resolution ladder on `(ℤ/p)*`, reading more than the lowest digit) are built
∅-axiom beyond `d = 2` is open; the cyclic infrastructure (`primitive_roots.md`)
supports them, but only the resolution-2 readout is closed.
