# Addition and multiplication are two faces of one count

The prime-exponent vector `vp` is a single count-Lens readout.  Multiplication *adds* its
components; the difference-of-powers *minimizes* them.  Lifting-the-exponent is the exact
statement of how the difference operation moves that one count — nothing analytic, all counting.

## 213-native answer

`vp p n` is the count-Lens reading of the prime-power axis at `p`: the largest `k` with `pᵏ ∣ n`
(`seed/AXIOM/06_lens_readings.md` §6.7), characterized internally by
`le_vp_iff : pᵏ ∣ n ↔ k ≤ vp p n` (`lean/E213/Meta/Nat/Valuation.lean`).  This one readout has two
behaviours, one per operation:

- **Multiplication adds it**: `vp p (m·n) = vp p m + vp p n`
  (`PrimeValuation.vp_mul`).  This is the `×`-count-Lens — the exponent vector is *the* faithful
  multiplicative readout (`theory/essays/synthesis/multiplicativity_is_the_x_count_lens.md`),
  faithful because the axes separate (`vp_separation`, which *is* unique factorization).
- **Addition minimizes it**: if `vp p x < vp p y` then `vp p (x+y) = vp p x`
  (`LiftingExponentPP.vp_add_eq_min`).  A sum sits at its uniquely-least-counted term: `pᵏ` divides
  the small term hence the sum; the next power divides the large term but not the small, so it
  cannot divide the sum.

These are not two lemmas about two structures.  They are the two ways one count responds to the
two operations — the ultrametric law is the additive shadow of the same `vp` whose multiplicative
shadow is multiplicativity.

## Derivation — lifting-the-exponent is these two faces meeting

`v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)` (`LiftingExponentGeneral.lte`) is exactly where both faces are
forced into one equation.  Write `a = b + d`, `d = a − b`.  The two-variable binomial theorem
(`BinomialTwoVar.add_pow`) splits the difference:

```
(b+d)ⁿ − bⁿ  =  n·b^{n−1}·d  +  R,    R = Σ_{k≥2} C(n,k) b^{n−k} dᵏ.
```

Now the *multiplicative* face reads each term: the middle term's count is `vp(n) + vp(d)` (counts
add over the product `n·b^{n−1}·d`, with `vp(b)=0` since `p∤b`); every tail term carries `dᵏ`
(`k≥2`), so its count is at least `2·vp(d) > vp(d)+vp(n)` — strictly more, once the prime case
supplies the extra factor from `p ∣ C(p,k)`.  Then the *additive* face (`vp_add_eq_min`) reads the
whole sum: the middle term is uniquely least, so it pins the answer.  The general theorem assembles
by iterating the prime kernel (`vp_pow_pk`) and factoring `n = pᵏ·m` (`LiftingExponentGeneral.lte`)
— the `+ vp(n)` is the exponent's *own* count entering through the iteration.

So LTE is not a fact *about* valuations added on top of arithmetic; it is the single count `vp`
being read once multiplicatively (to weigh each binomial term) and once additively (to select the
minimum).  The lemma is the handshake of the two faces.

## Dual function

Classically, lifting-the-exponent is a `p`-adic valuation lemma proved by induction with a
mod-`p²` expansion — a result *about* the `p`-adic numbers.  The packaging stripped: there is no
`p`-adic completion here, no analytic limit; `vp` is a finite count and LTE is a finite identity
between counts.  213's reading is sharper in saying *why* the `+1` per prime factor appears — it is
the multiplicative face (`p ∣ C(p,k)` lifting each tail term) feeding the additive face
(`vp_add_eq_min` selecting the unique minimum), the same count read two ways in one step.

## Cross-frame connections

The same `p ∣ C(p,k)` appears at two resolutions: mod-`p` it gives Freshman's dream
`(a+b)ᵖ ≡ aᵖ + bᵖ` (`DyadicFSM/FLT/FreshmanDream`); to all orders it gives LTE's exact valuation.
Freshman's dream is LTE's binomial tail read at one-bit resolution (`mod p` — the tail vanishes);
LTE is the same tail read by the full count.  Four nodes, one structural fact: `vp_mul` (× face),
`vp_add_eq_min` (+ face), `prime_dvd_choose` (the bridge that makes the tail's count strictly
larger), and `vp_separation` (the faithfulness that lets "count" mean anything at all).

## Open frontier

The reading "addition minimizes, multiplication adds" is the rank-1 (single-prime) statement.
Its multi-prime form — the exponent *vector* under `+` taking a componentwise min-with-correction
— is what an abstract "any multiplicative function is forced by descent over the UFD vector" would
need; that abstraction remains open (`multiplicativity_is_the_x_count_lens` open frontier).  And
`p = 2` is excluded: the additive face's "strict minimum" fails when the two least terms tie, which
is exactly the `v_2(a+b)` correction the `p=2` LTE variant carries.
