# The Teichmüller representative — a forced fixed point of the Frobenius self-map

## Triggering question

> "What is a `(p−1)`-th root of unity (a Teichmüller representative) in
> 213?  In what sense is `ω(x)` the fixed point of `x ↦ x^p`, and how is
> it reached without a completion step?"

## 213-native answer

A `(p−1)`-th root of unity in `ℤ_p` is **the fixed point that the
self-map `x ↦ x^p` is forced into**, read off as the diagonal of its own
approximant sequence.  Concretely `ω(x) : ZpSeq p` is
`Zp.teichmuller p hp x`, defined by **one line** — the diagonal of the
iteration `iter x n = x^(p^n)`:

```
ω(x).digits k := (teichmuller_iter x k).digits k
```

(`lean/E213/Lib/Math/NumberSystems/Padic/Teichmuller.lean`).  It is
pinned by two facts: `ω(x).digits 0 = x.digits 0`
(`teichmuller_digit_zero`) and the Frobenius fix
`(ω(x)^p).trunc n = ω(x).trunc n` for all `n` (`teichmuller_pow_p_trunc`).
The second is the defining equation `ω^p = ω`.  For a unit `x` it refines
to `ω(x)^(p−1) ≡ 1` (`teichmuller_pow_pred_trunc`): `ω(x)` is a
`(p−1)`-th root of unity, and the group `μ_{p−1}` is exactly the set of
Frobenius-fixed points.

## Derivation

The self-map is `Frob : x ↦ x^p`.  Its iterates do not stand still at any
finite stage — but they **settle digit by digit**:
`(iter x (n+1)).trunc (n+1) = (iter x n).trunc (n+1)`
(`teichmuller_iter_cauchy`).  Each application of `Frob` freezes one more
digit (the digit-0 case is Fermat, `pow_p_trunc_one`; the inductive step
is the binomial-free Frobenius lift `frobenius_lift`).  So the iteration
is a self-reference that *completes*: it reaches a limit and stays there.

This is precisely the **Nat-style (Lambek-like) self-reference** of
`seed/AXIOM/05_no_exterior.md` §5.2 — "the iteration reaches its limit
and stays there… the loop is also a fixed point" — as opposed to the
Bool-style liar loop that only oscillates.  `Frob` on a unit is Lambek,
not liar: it has the fixed point `ω`, and the iteration converges to it.

The subtle move is *how* the limit is obtained.  There is no completion
functor, no inverse-limit existence axiom.  The Cauchy identity **is** the
trunc-recursion of the diagonal:
`ω(x).trunc (n+1) = (iter x n).trunc (n+1)` (`teichmuller_trunc_succ`),
whose step case is `teichmuller_iter_cauchy n` verbatim.  The limit
"reached by none of the approximants" is read directly off the approximant
family as its diagonal — the internal handle that
`seed/AXIOM/05_no_exterior.md` §5.4 instructs us to find before declaring
a wall.

## Dual function

This is the classical Teichmüller representative with its packaging
removed.  Classical construction: take the inverse limit `lim_n ℤ/p^n`,
prove the sequence `x^(p^n)` is Cauchy there, invoke completeness to name
the limit, then prove it satisfies `ω^p = ω`.  The 213 reading keeps the
content (`x^(p^n)` Cauchy, `ω^p = ω`) and drops the import (completeness
as an existence step).  Sharper: the limit is not *asserted to exist* and
then characterized — it is *exhibited* as a concrete `ZpSeq` whose every
digit you can `#eval`, and `ω^p = ω` falls out by chaining `pow_trunc` +
`teichmuller_iter_cauchy`, no completeness invoked.  The "representative"
is not a chosen coset member; it is the unique Frobenius-fixed point, and
uniqueness is the Hensel unit-cancellation (`teichmuller_pow_pred_trunc`
via `mul_right_cancel_trunc`, `Padic/TeichmullerUnit.lean`).

## Cross-frame connections

The same structural fact appears in four frames:

- **Frobenius fixed point** `ω^p = ω` (p-adic, `teichmuller_pow_p_trunc`).
- **Möbius fixed point** `P(φ) = φ`, the attractor of the
  self-description iterator (`seed/AXIOM/05_no_exterior.md` §5.6,
  `lean/E213/Lib/Math/Algebra/Mobius213.lean`, essay
  `theory/essays/p_orbit/mobius_self_form_fixed_point.md`).
- **Nat-style self-reference completes** — the catamorphism reaching its
  limit (`seed/AXIOM/05_no_exterior.md` §5.2).
- **The residue reached by no pointing** —
  `Lens/FlatOntologyClosure.object1_not_surjective`: pointings only
  converge, none lands on the limit.

The fourth frame marks where `ω` is *complementary* to the residue
itself.  The flat-ontology closure says the residue is reached by no
approximant — the limit is outside every pointing's image.  The
Teichmüller diagonal is the opposite case: here the limit *is* internally
reached, because each digit settles at a finite stage, so the diagonal
collects genuinely-attained values into a genuine `ZpSeq`.  The general
rule (`object1_not_surjective`) is "the limit is reached by none";
`ω(x)` is the special situation where the per-digit pointings each
terminate, so the diagonal of attained digits is the limit.  Frobenius
convergence is the case where "reached by none" relaxes to "reached
digit-wise, assembled by the diagonal."

## Open frontier

The Frobenius fix and `μ_{p−1}` membership are closed at the truncation
level.  The *sequence-level* uniqueness of the `ω·u` factorisation
(`ℤ_p^× ≃ μ_{p−1} × (1+p·ℤ_p)` as `ZpSeq`, not just at every `trunc n`)
hits the same trunc-vs-sequence boundary as the ring-axiom layer —
possibly a quotient construction outside strict-∅, possibly an imported
residue that trunc-level is the native form of.  Tracked under
`research-notes/frontiers/`.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.NumberSystems.Padic.TeichmullerUnit
python3 tools/scan_axioms.py \
  E213.Lib.Math.NumberSystems.Padic.Teichmuller \
  E213.Lib.Math.NumberSystems.Padic.TeichmullerUnit
```

Chapter: `theory/math/numbersystems/padic_real213.md`
("The explicit representative `ω(x)`" + "as a root of unity").
