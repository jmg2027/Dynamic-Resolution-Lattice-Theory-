# Equality is a certificate

Two numbers are equal not because something hands you "the same," but
because a **checkable certificate** says so — and the certificate's
content is the structure of the number itself.

## 213-native answer

There is no enclosing frame to declare two things identical for free, so
"`m = n`" is exactly the certificate that proves it.  For positive naturals
that certificate is the prime-exponent reading: `m = n` holds exactly when
`vp p m = vp p n` at every prime `p` (`Meta/Nat/VpSeparation.vp_separation`
— unique factorization, stated as the faithfulness of the `vp`-coordinate).
For powers the certificate is sharper still: `a^r = b^q` exactly when the
two exponent-vectors point the same way, `r·vp p a = q·vp p b` at every
prime (`Meta/Nat/FoldCriterion.pow_eq_pow_iff_vp`).  The content of "equal"
is the object's own structure — its prime exponents.

## Derivation

Equality is built, not given, and it is built from order.  At the discrete
floor a number is *located* by a strict two-sided pinning — the unique
point in the gap between `a` and its next-next, `a < e < a+2 ⟹ e = a+1`
(`Meta/Nat/StrictLocate213.locate_strict`); equality is then the conjunction
of two such strict bounds (`Int213.eq_of_sandwich`), so the sandwich, not
the equation, is the proper probe (`theory/math/numbersystems/slot_arithmetic.md`
§2).  "`m = n`" at this level is the certificate "each pins the other in a
unit gap."

One rung up, at multiplication, the certificate changes shape but not
character.  `vp_separation` says the full prime-exponent vector *determines*
the number: matching readings at every prime is a certificate of equality,
and `FoldCriterion.pow_eq_pow_iff_vp` makes it an iff for powers.  Where the
axes are independent the certificate is decisive in the other direction too:
distinct primes give independent axes, so `p^a = q^b` forces `a = b = 0`
(`FoldCriterion.prime_pow_unique`, with `two_three_unique` its `2,3` case).
In every register the same move: equality is never free — it is checked by a
certificate (a strict sandwich for order, an exponent-vector match for
multiplication), and the certificate's content is the number's structure.

## Dual function

Classically equality is a primitive: reflexive, given, informationless.
Strip the enclosing frame that hands it over and what remains is exactly the
certificate that establishes it — which has *content* (which strict gap,
which prime exponents) and so a *cost*.  The refinement is that "equal"
becomes a graded, checkable relation whose price is the structure of the
thing, not a free axiom assumed at the start.

## Cross-frame connections

The continuum says the same.  With no line to inherit identity from, "two
pointings name one real" is as strong as the combinatorial certificate that
proves it — and that certificate has a **size**: the per-level Padé flip,
`48` at level one for the Lambert weld
(`theory/essays/analysis/when_two_pointings_are_one.md`, `weld_closed`).
So equality of reals (the weld's CF certificate), equality of powers (the
exponent-vector match, `pow_eq_pow_iff_vp`), and equality at the discrete
floor (the strict sandwich, `eq_of_sandwich`) are **one shape at three
resolutions**: equal ⟺ a certificate matches, and the certificate is the
object's own structure read out.  Reflexivity is the trivial certificate;
everything past it is paid for in structure.

## Open frontier

No single Lean statement yet packages "equal ⟺ certificate matches" with the
sandwich, the exponent-vector, and the weld's CF data as three instances of
one schema — the correspondence is recorded as a cross-domain bridge, not a
theorem.  The shared content (a certificate with a size and a shape) is
plain; the unifying object is unwritten.
