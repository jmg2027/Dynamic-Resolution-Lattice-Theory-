# §3. Form

The axiom is austere by design.  This chapter explains why each
of its features is forced and what algebraic shape the
combination takes.

## §3.1 Austerity as audit

Residual import is unavoidable the moment one writes anything in
language (§1.4), but the footprint can be minimised.  The
smaller the axiom, the sharper the contrast with anything that
slips in during derivation — if a result requires more than the
axiom itself, the gap is immediately visible against the
austere background.  The axiom plays the role of a contract:
*can everything be derived from just this?*

Austerity here is not poverty.  It is **auditability**.  A wider
axiom buries fudge inside its commitments; a narrow axiom forces
fudge into the open.

---

## §3.2 Why two, why binary

(The "two" in this section is the count-Lens reading of the
residue, not a Raw-level cardinality commitment.  Per §2.5, Raw
commits to no cardinality.)

Could one suffice?  No.  Distinguishing has nothing to operate
on without a second something for the first to be distinguishable
from.  A single Raw atom is not a state of the framework; it is
a state in which the framework has not begun.

Two, then, is the minimum count-Lens reading of a successful
first distinguishing.  Not "two somethings present prior to
distinguishing" — the count `2` *is* the residue of the first
distinguishing.

Could three or more be primitive?  No.  A third something is the
count-Lens reading of *further* distinguishing applied to the
existing residue; making it primitive imports cardinality where
distinguishing has not yet produced it.

Could the pairing be unary?  No.  A unary operation on one
something is self-reflexive and produces no new something —
nothing has been distinguished.

Ternary or more?  Reconstructible by repetition of binary.  No
reason to treat as primitive.

So **two + binary** is the unique minimum count-Lens shape that
the first distinguishing admits.  Not a chosen pair of numbers,
but the only reading the operation allows.

---

## §3.3 Why symmetric, why anti-reflexive

The pairing is **symmetric**.  There is no basis for assigning
an absolute order to `a/b` versus `b/a`.  Distinguishing the two
sides would silently import a criterion for which comes "first,"
and the axiom supplies no such criterion.

The pairing is **anti-reflexive**.  `x/x` is undefined.  Pairing
something with itself does not create an object of distinction —
the thing is not distinguished from itself.  Allowing `x/x`
would directly contradict the content of clause 1 (primitive
distinction).

---

## §3.4 The forcing chain: 1 → 2 → 3 → 4

The four clauses of §2.4 are not four independent choices.  Each
is forced by the prior.

  - **Clause 1 → Clause 2.**  Once distinguishing operates, the
    residue of distinguishing is itself a something.  If it were
    not, the operation would have no residue to record,
    contradicting clause 1.
  - **Clause 2 → Clause 3.**  The residues `a/b` and `b/a` refer
    to the same distinguishing event.  Treating them as distinct
    would silently import an absolute order, for which clause 1
    supplies no basis.
  - **Clause 3 → Clause 4.**  If `x/x` were defined,
    distinguishing would be claimed where clause 1 supplies no
    operand (nothing to distinguish from).  The operation
    collapses.

So fewer than four clauses cannot record distinguishing-yields-
residue, and more than four would add what is already derived
from these.  Four is not the result of taste; it is **the**
number that closes the operation.

---

## §3.5 Algebraic signature — the Möbius form

The four-clause restatement admits a compact algebraic encoding
as the Möbius matrix

```
P = [[2, 1],
     [1, 1]]
```

with iterator `P(x) = (2x + 1) / (x + 1)`.  The entries record
the axiom's content directly:

  - `2` — two somethings, `a` and `b`.
  - `1` — identity preservation (`det P = 1`).
  - `trace P = 2 + 1 = 3 = NS` (the spatial-axis cardinality).
  - `discriminant = trace² − 4 · det = 9 − 4 = 5 = NS + NT`
    (the atomicity sum).
  - `eigenvalues = (3 ± √5) / 2 = φ², 1/φ²`.

The Möbius iterator is the natural algebraic form of the "two +
binary" choice (§3.2).  Its fixed point φ = (1 + √5) / 2 is the
residue of self-pointing iteration — the algebraic embodiment of
"the minimum fixed point of self-reference" that §5.6 describes
in detail.

The same φ appears in DRLT physics (the CKM phase δ, the Cabibbo
angle, neutrino mass ratios) and at the asymptote of the algebra
tower.  This cross-domain consistency is not coincidence: it is
the same Lens result reading the same residue from different
framings.

This is an **interpretation**, not an addition.  The bridge
theorem at `lean/E213/Lib/Math/Mobius213.lean` is ∅-axiom — the
algebraic encoding is derivable, not imposed.  The four clauses
remain the minimum-commitment statement; §3.5 records an
algebraic *consequence*.

A reminder: the matrix admits two simultaneous Lens readings
(frozen + dynamic), discussed in §5.7.  The same parametric
`configCount : Nat → Nat` family in
`seed/RESOLUTION_LIMIT_SPEC.md` realises the same point at a
different level — its values agree across routes because they
read the same residue, not because external coincidences align.
