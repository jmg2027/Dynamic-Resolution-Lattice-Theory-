# 4 · Two transports, one square

## Sign and remainder are readouts, not choices

Instantiate the witness layer at the list's two progressive
operations and the first two classical extensions appear — with
their famous appendages exposed as witness readouts.

**The difference layer** (+-pairs).  Every oriented pair is witnessed
from exactly one side: either `a + x = b` has a solution or the
*swapped* equation does, never both
(`Int213.witness_total`, `witness_not_both`).  The **sign** is the
name of that side (`subNatNat_eq_ofNat_iff`, `subNatNat_eq_negSucc_iff`)
— a 2-valued readout of the witness's location, not a new primitive
and not a convention.

**The ratio layer** (×-pairs).  The ×-question may miss, but the
÷-sandwich always locates, and the gap it leaves has `a` rungs: the
**remainder** is the position in that gap, an `a`-valued readout,
with the exact witness existing precisely when it vanishes
(`NatDiv213.div_sandwich`, `mul_witness_iff_mod_eq_zero`).  Sign and
remainder are the same kind of object at two layers — obstruction
readouts — and reduction to lowest terms is the layer's *possibility
theorem* (`Gcd213.gcd_strip_coprime`, `coprime_repr_unique`, via the
Bezout-free Euclid chain `gcd213_mul_left` →
`coprime_dvd_of_dvd_mul`), not its ontology.

Each layer is **closed under its own operation's questions**
(`Int213.subNatNat_add_witness`, `RatioLensFounding.ratio_mul_witness`):
new numbers only ever come from *another* operation's question.

## The signed rationals

Mixing the two layers has one genuine subtlety, and it is an order
phenomenon: cross-`≤` does not descend through the sign — a
nonpositive factor reverses the order
(`OrderMul.mul_le_mul_right_nonpos`).  So the signed layer reads the
sign off first and compares magnitudes on the positive cone:
existence and uniqueness of the sign-carrying lowest form
(`Rat213.lowest_exists`, `lowest_unique` — mixed-sign cases die by
bare constructor clash: the sign readout is rigid), and the derived
order is well-defined exactly there
(`ratioLeZ_descends`, `ratioLeZ_iff`).

## The square commutes, and the reason is distributivity

There are two routes to the signed rationals — differences of ratios,
ratios of differences — two bracketings of ℕ⁴.  They agree, and the
*reason* they agree is not a coincidence to verify but a law to name:

> **Distributivity is the commutation law of the two pair-Lenses.**
> The difference fiber is a +-action, the ratio fiber a ×-action, and
> `k(a+c) = ka + kc` says the ×-transport carries +-orbits to
> +-orbits.

`Rat213.qdiffEquiv` (the difference-of-ratios leg, written without a
single subtraction) corresponds exactly to the ratio-of-differences
leg under the comparison map (`square_commutes`), and with positive
denominators both routes land on the *same* lowest representative
(`qdiff_same_lowest`, via `ratioEqZ_trans`).  The proof content is
two keystones and distributivity shuffles — nothing else.

One more classical artifact dissolves on the way.  The familiar
"two-sided" linear equation `a·x + b = c·x + d` — four slots — is not
a postulate about equations needing two sides.  Unfold the pair
product and **the two sides are the two components of the pair
slots** (`Int213.subNatNat_mul_eq_iff`): `2x = −5` and `2x = 5`
differ only in which side a `5` sits.  The pair ontology was inside
the school notation all along.
