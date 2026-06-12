# The certificate boundary — when a recurrence carries its own proof

A recurrence has a **certificate** when its truth is a single finite object you
can point at: a function `Ĝ(j,k)` whose forward difference *is* the recurrence's
summand combination.  Certifiability ends at one named place — the
hypergeometric/harmonic boundary — and that place is the same one where the
arithmetic logarithm turns from algebraic to archimedean.

## 213-native answer

A holonomic recurrence `Σ_k F(j,k) = 0` (the summand `F` a combination of shifts
of one term) is **certified** by a function `Ĝ(j,k)` with

```
F(j,k) = Ĝ(j,k+1) − Ĝ(j,k)        (the telescoping witness)
```

— then summing over `k` collapses to the boundary `Ĝ(j,top) − Ĝ(j,0)`, and if `Ĝ`
vanishes there the recurrence *is* `0 = 0`.  The certificate is not a proof
strategy but the proof itself made syntactic: a fixed expression (here a
polynomial times binomials) that a reader checks by one difference computation.
This is the WZ object behind Apéry's recurrence
(`theory/math/numbertheory/apery_zeta3_arithmetic.md`):
`Ĝ(j,k)=−4k⁴(2j+3)(4j²+12j−2k²+3k+8)·C(j+2,k)²·C(j+k,k)²`, with
`(j+1)²(j+2)²·F(j,k)=Ĝ(j,k+1)−Ĝ(j,k)` verified, then re-derived ∅-axiom in
`AperyRecurrence.lean` (`per_k`, `sumTo_shift_eq`).

## Derivation — why this `B` is certifiable

The certificate exists exactly when the summand is **proper hypergeometric**: the
ratio `F(j,k+1)/F(j,k)` is a *rational function* of `(j,k)`.  The denominator Apéry
summand `a(n,k)=C(n,k)²C(n+k,k)²` is built from `choose`, whose consecutive ratios
are rational (`colrec`: `(n+1−k)C(n+1,k)=(n+1)C(n,k)`, `lowrec`:
`(k+1)C(n,k+1)=(n−k)C(n,k)` — `AperyRecurrence.lean`).  Rational ratios are what
Gosper/Zeilberger telescoping needs; the certificate is then forced and finite.
Equality, here, is paid for in a fixed-size structure — the certificate is the
exponent-vector/order-sandwich analogue at the level of *recurrences*
(`theory/essays/synthesis/equality_is_a_certificate.md`): the recurrence's truth is
a checkable witness whose content is the summand's structure.

## Dual function

This is the Wilf–Zeilberger certificate with the dichotomy "does an algorithm find
it?" dropped: certifiability is not a property of our search but of the summand —
a single difference equation `F = ΔĜ` either has a hypergeometric solution `Ĝ` or
it does not.  213 sharpens the classical reading by naming *the obstruction*: the
boundary is the summand leaving the proper-hypergeometric class, which is a
structural fact about the term, not about Zeilberger's algorithm timing out.

## Where certifiability ends — the harmonic boundary

The numerator Apéry number `A(n)=H₃(n)·B(n)+K(n)` satisfies the **same** order-2
recurrence, yet has **no clean certificate** — every candidate (`cert_A`, the
kernel `cert_K`, even `cert_A − cert_B·c`) is an irreducibly messy rational, not a
fixed polynomial-times-binomials.  The break is exactly the harmonic factor
`H₃(n)=Σ_{j≤n} 1/j³`: it is not hypergeometric in `n` (its term ratio is not
rational), so the product summand leaves the certifiable class.  The recurrence
still holds — but only by explicit kernel telescoping, not a finite witness.

## Cross-frame connections

The boundary is one fact in three frames.  (i) **Hypergeometric / harmonic** —
certifiable vs not.  (ii) **Algebraic / archimedean log** — `H₃` is a sum of
`1/j³`, i.e. values of the *archimedean* place, the transcendental `ln|·|`; the
213 logarithm is `vp`, finite-support and certifiable on the algebraic places,
unbounded only at the archimedean one (`theory/essays/analysis/what_is_a_logarithm.md`).
A summand is certifiable while its content stays on the algebraic (finite-`vp`)
side and loses the certificate when an archimedean-log factor enters.  (iii)
**Rank-2 forced form** — the order-2 recurrence's Casoratian is forced (a unique
alternating form on a rank-2 space, `theory/essays/analysis/the_form_forced_by_two.md`);
the *shape* (one Casoratian `6·(m!)⁶`, `Zeta3Cut.zeta3_cross_det`) is forced for both
numerator and denominator, but only the denominator's *summand* is certifiable —
shape is forced by rank, certifiability by the term class.  The same divide
(hypergeometric = algebraic = certifiable, harmonic = archimedean =
explicit-only) reads through all three.

## Open frontier

The numerator side is the live work: the kernel inhomogeneous recurrence needs the
explicit Apéry telescoping (no certificate to verify), with the `H₃` part already
cleared from `apery_recurrence` (`Zeta3Numerator.harmonic_part_recurrence`).  That
`zeta3HolonomicReal` waits on a *harmonic* recurrence with no finite witness is the
constructive statement of where this boundary bites.
