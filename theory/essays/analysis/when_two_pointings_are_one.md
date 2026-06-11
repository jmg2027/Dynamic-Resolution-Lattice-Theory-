# When two pointings are one

Two approximant sequences "converge to the same real" means: their limit
cuts agree on every probe.  That agreement is not inherited from a real
they share — it is a theorem with a price, payable per level, in exact
combinatorial coin.

## 213-native answer

A real is a pointing's residue-internal record — a fold with brackets and,
when it completes, a limit cut `limit m k : Bool` read at every rational
probe (`theory/math/numbersystems/real213.md`,
`theory/math/analysis/modulus.md`).  No pointing reaches the real: the
residue is outside every view's image
(`FlatOntologyClosure.object1_not_surjective`, cited through
`theory/lens/unified_equivalence.md`).  So when two pointings — say the
Lambert continued fraction of `coth(1/q)` and its series ratio — are said
to point at one real, there is no shared object to appeal to.  The only
available content of "one real" is **probe-wise agreement of the limit
cuts**:

```
(cothSeriesCauchySep q hq).limit m k = (cothUnitCFCauchySeq q hq).limit m k
```

— `weld_closed`, `theory/math/analysis/lambert_weld.md`.  The equation IS
the identity of the two pointings' targets; there is nothing further it
abbreviates.

## Derivation

Equality of reals, like every 213 equality, decomposes along the one
Lens-arrow (`theory/lens/unified_equivalence.md`): two readings are "the
same" exactly when each refines the other on every admissible probe.  For
completed folds the admissible probes are the rational pairs `(m, k)`, and
the refinement condition is the displayed Boolean equation, quantified
over all of them.  This sets the proof obligation: not "both converge to
`coth(1/q)`" (which would smuggle the unreached object in as a premise)
but a two-sided order transfer between the approximant families
themselves.

The worked theorem shows what that costs.  One direction is soft: the
series sits below every odd CF convergent (`series_le_odd`), so a CF
failure forces a series failure.  The other direction compresses into a
single base family (`LowerBase`), and the base family's proof is an exact
ledger (`theory/math/analysis/lambert_weld.md` §4–§6): at each level `i`
the two coefficient lists agree entry-by-entry past a diagonal, and at
the diagonal the B-side exceeds the A-side by exactly
`cfpos n n = (4i+2)!!` — the Padé remainder, surviving as one
double-factorial.  That single flip then pays for every sub-diagonal
discrepancy with tenfold room (`2i·(4i+1)!! ≤ (4i+4)·(4i+2)!!`).
Agreement of the two pointings is, concretely, *this number being large
enough* — the identity of two presentations of a real has a witness you
can evaluate: `48` at level one.

That the price is presentation-shaped, not real-shaped, is the
`PresentationDependence` reading
(`Real213/PresentationDependence.lean`, `rcut_rescale`): modulus,
holonomicity, certificate depth are properties of the pointing.  Here the
property doing the work is the Lambert CF's linearly growing partial
quotients — they make the cross-determinant floor an effective separation,
which is why the weld closes hypothesis-free at modulus `k+2` while π's
pointings, growth-structureless, defeat every schedule
(`wallis_no_graded_certificate`).  Two pointings of *e*-family values can
be welded; nothing in the result says every pair of pointings of every
real can be.

## Dual function

Stripped of packaging, this is the classical uniqueness-of-limits — but
classically that fact is free, inherited from the real line both sequences
already live in, and so it carries no information.  Read 213-natively the
same statement becomes load-bearing: with no enclosing line, uniqueness is
exactly as strong as the combinatorial identity that proves it, and it
localizes — *these two* pointings, welded by *this* flip value, at *this*
modulus.  The refinement is that "the same real" acquires a certificate
with a size.

## Cross-frame connections

The diagonal flip is the `cross = 1` regime of the one pair-layer cross
expression: held at `0` the cross-equation mints an equivalence class (a
number); held at `1` it is the unimodular floor that keeps two pointings
separated until welded; held `≥ 1` it is a margin.  Equality-as-refinement
(`unified_equivalence`), the det-one floor (`cf_det_even_nat` descended),
and the weld's flip are one expression read at three values.  And the
overall shape — identity claimed between two views, provable only by an
internal transfer because the common object is reached by none — is
`object1_not_surjective` at the analysis scale: the same fact that makes
"which view is the residue?" ill-posed makes "do these pointings agree?"
a real theorem.

## Open frontier

The weld certifies one pair of pointings.  A second, bridge-free
certificate route (the proven `i`-invariant `weld_casoratian` identity:
flip criterion + ratio descent) is open, as is the general question of
which pointing-pairs of a given value admit any weld at all — the
partial-quotient growth reading suggests the answer is again a property
of the pair of presentations, not of the value.
