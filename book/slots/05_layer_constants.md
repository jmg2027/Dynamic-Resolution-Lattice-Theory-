# 5 · Layer constants — √2 and i are siblings

## Slots have layers

Once the difference and ratio layers exist, questions can be asked
*with pair-valued slots*.  This is the whole story of the "higher"
number systems, and it needs no new mechanism — only the observation
that **the question's slot layer sets the solution's budget**, and
the ordinary witness dichotomy does the rest.

Three ×-slot questions with pair slots, side by side:

| question | witness at the current layer? | result |
|---|---|---|
| `(a,b) + x = (c,d)` | always (`subNatNat_add_witness`) | nothing new |
| `(a,b) · x = (c,d)` | generally no (`2x = −5`) | the signed rationals: four naturals |
| `x^(n,n+2) = (m+1,m)` | never (squares don't cross the sign) | a constant: `i` |

The third row deserves its plain statement.  Over ℕ-slots no
imaginary number can arise — `x² = −1` simply *is not an
ℕ-question*; two ℕ-folds never cross in that direction
(`CompletionDichotomy.int_sumSq_eq_zero` is the certificate).  What
classical notation writes as `x² = −1` is a question **whose slots
are already +-pairs**, `x^(n,n+2) = (m+1,m)`, and by the same slot
rule its solution is a number with two pair-slots — four naturals.
Likewise `x^(2/1) = 2/1` has no witness among the ratio pairs, so
`√2 = ((2,1),(2,1))`.  Hence:

> **`i` is to +-pair slots what `√2` is to ×-pair slots** — sibling
> constants of sibling layers, distinguished only by which pair layer
> their slots come from.

"Constant" is meant exactly: in `x^(n,n+2) = (m+1,m)` both orbit
coordinates are fixed; `n` and `m` are pure fiber.  Zero effective
slots — `i` is a constant of its layer the way `2` is a constant
of ℕ.

## The four-axis product

The imaginary axis is not ×-closed over bare ℕ-components: multiply
and the +-pair structure is dragged into the real component.  The
closed object is the four-axis nested tuple, and its product is
written without one subtraction sign (`GaussTuple.gmul`).  Two facts
pin it:

* `gmul_i_i` : `i ⊗ i` **is** the +-inverse unit — definitionally,
  by `rfl`.  No quotient, no reduction; a literal equality of tuples.
  The new axis folds back into the +-inverse axis at depth 2, which
  is why the axis count stops at two per component.
* `gmul_readout` : read through the difference-Lens, the tuple
  product is exactly the classical complex product.  The readout is a
  Lens *on* the tuple; it is not what the tuple *is*.

## Fibers transport; they do not vanish

A pair-slot is one orbit coordinate plus one fiber coordinate, and a
natural worry is what becomes of the fiber when a question is asked
through it.  The answer is the volume's prettiest small theorem
(`PairPow.pairPow_fiber`, `pairPow_id`): with the subtraction-free
pair exponent `(p,q)^(c,d) := (p^d·q^c, q^d·p^c)`,

> riding the exponent's +-orbit lands the value on its own ×-orbit:
> `(p,q)^(n,n+1) = ((pq)^n·p, (pq)^n·q)`.

The exponent's fiber coordinate is not lost and not meaningless — it
**transports** into redundancy the value already carries.  Counting
slots correctly therefore means counting orbit coordinates; raw
naturals over-count by exactly the riding.

## Visibility is per frame

One caution, learned adversarially.  "`x² = −1` has no answer" is a
statement *at* a frame — the sign, remainder, and order readouts.
The wrap frames see it: at every prime `p ≡ 1 (mod 4)` there is `x`
with `p ∣ x² + 1` (`ModArith/QRNegOne.qr_neg_one`; `2² + 1 = 5`).
Whether a question's obstruction is visible is itself a per-frame
readout — the Legendre symbol — and the celebrated reciprocity law
is the law of *that* readout.  Rigidity is a property of the
(question, frame) pair, never of the question alone.
