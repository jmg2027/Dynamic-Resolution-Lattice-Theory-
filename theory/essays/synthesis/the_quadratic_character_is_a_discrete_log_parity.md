# The quadratic character is a discrete-log parity

`(a/p)` is the count-Lens parity of the discrete logarithm of `a` in the
cyclic group `(ℤ/p)*`: fix a generator `g`, write `a = g^k`, and `(a/p) =
(−1)^k`.  The Legendre symbol is "even or odd position in the single orbit of
the units."

## 213-native answer

The units `{1,…,p−1}` are not a bag with a residue/non-residue predicate
stapled on from outside.  They are **one orbit**.  A primitive root `g` exists
(`primitive_roots.md`, `exists_primitive_root`), and its powers
`g⁰, g¹, …, g^{p−2}` list every unit exactly once.  So each unit `a` carries a
single datum — its position `k = dlog_g(a)` in the orbit — and the quadratic
character is the **mod-2 readout** of that position:

```
(a/p) = (−1)^{dlog_g(a)}.
```

A square is an even position (`a = (g^j)² = g^{2j}`); a non-residue is an odd
one.  The whole QR/non-QR split is the count-Lens (`seed/AXIOM/06_lens_readings.md`)
reading the orbit-position counter at resolution 2.

## Derivation

That this parity is well-defined and *forced* — not posited — is the content.
The orbit has even length `p−1 = 2m`.  Its unique order-2 element is `p−1 ≡
−1`, and `g^m` (order exactly 2, since `g` has order `2m`) must be it: `g^m ≡
−1`.  Therefore

```
a^m = g^{km} = (g^m)^k ≡ (−1)^k,
```

so **Euler's criterion is the discrete-log parity in disguise**:
`a^m ≡ 1 ⟺ k` even `⟺ a` a square (`legendre_symbol.md`,
`quadratic_reciprocity.md`).  The same `k mod 2` surfaces as a permutation
sign: multiplication-by-`a` is `σ_a = σ_g^k`, and `σ_g` is a single
`(p−1)`-cycle of sign `−1` (`primitive_roots.md`, `ZolotarevCycle.zolotarev_full`,
`psign_mulPerm_primitive`), so `psign σ_a = (−1)^k = (a/p)` — Zolotarev's
lemma, read off the orbit rather than off the symmetric cross-count of
`zolotarev.md`.

The character's two defining properties dissolve into orbit arithmetic.
Multiplicativity `(ab/p) = (a/p)(b/p)` is `dlog` carrying products to sums
(`dlog_g(ab) = dlog_g(a) + dlog_g(b)`) and `(−1)^·` carrying sums to a parity
product.  Existence is just the orbit having even length so that "even vs odd
position" is a `{±1}`-valued function at all.

## Dual function

Classically one says "the Legendre symbol exists, is multiplicative, and
detects squares."  Stripped of packaging, all three are one fact about a
cyclic group of even order: the position counter has a mod-2 readout, that
readout is additive-to-multiplicative, and even positions are exactly the
squares.  213's sharpening is that there is no separate "symbol" object — the
character is the count-Lens applied to the discrete log, and a primitive root
is the witness that the log is defined on every unit.

## Cross-frame connections

One bit `k mod 2`, four co-equal readouts:

- **Euler power** `a^m ≡ (−1)^k` (`legendre_symbol.md`);
- **permutation sign** `psign σ_a = (−1)^k` (`zolotarev.md`, and via the
  generator cycle, `primitive_roots.md`);
- **determinant** `det(permMatrix σ_a) = psign σ_a` (`zolotarev.md`,
  `det_permMatrix`);
- **discrete-log parity** `(−1)^{dlog_g(a)}` (`primitive_roots.md`).

And the **Fibonacci rank of apparition** reads the same bit at `a = 5`:
`α(p) ∣ p − (5/p)`, so the entry point of the golden recurrence is offset by
the parity of `dlog_g(5)` — the discrete-log face of the permutation-sign
reading in `the_fibonacci_rank_is_a_permutation_sign.md`.  The quadratic
character is one residue self-pointing, read five ways.

## No-exterior reading

The QR/non-QR distinction is not a predicate imported onto the units; it is
the units pointing at themselves through the count-Lens.  The squares are the
index-2 sub-orbit `⟨g²⟩`, and a generator is a non-residue precisely because
its order `2m` does not divide `m` (`primitive_not_qr`) — the orbit cannot
fold the generator into its own square-half.  There is no smaller-than-itself
description of the character: it is forced by the orbit being cyclic of even
order, the same `object1_not_surjective` shape that makes the residue reachable
by no single view (`seed/AXIOM/05_no_exterior.md` §5.1).

## Open frontier

The equality `(a/p) = (−1)^{dlog_g(a)}` as a single Lean theorem — tying
`exists_primitive_root` to the standing `psign`/Euler readouts — is buildable
and not yet built (the ripest edge in the Zolotarev cross-domain board).  Once
landed it makes "the character is a discrete-log parity" a theorem, not a
reading.
