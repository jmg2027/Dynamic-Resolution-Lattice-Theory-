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

Neither feature is a constraint imposed on a pairing mechanism
that could have behaved otherwise.  Symmetry records an
*absence* (no order criterion exists to separate `a/b` from
`b/a`); anti-reflexivity records an *absence* (no operand exists
for self-distinguishing).  Both are read off the completed act
of §2.3, not bolted onto a machine.

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

The arrows of the chain are **logical forcing, not temporal
stages**.  Nothing happens "first" in the act of pointing — all
four clauses are simultaneously present (§2.3, §5.5).  The chain
is the order in which an *explanation* walks the one complete
event, the same expository shadow that §2.2 notes for the
notation `a`, `b`, `a/b`: a Lens reading of the act after the
fact, not the act's internal sequence.

---

## §3.5 Algebraic signature — the residue has a name

The four-clause restatement, taken together, admits a compact
algebraic encoding.  The Möbius matrix

```
P = [[2, 1],
     [1, 1]]
```

with iterator `P(x) = (2x + 1) / (x + 1)` records the axiom's
content directly.  The constant `2` is two somethings; the
constant `1` is identity preservation (`det P = 1`).  The trace
`2 + 1 = 3` reads as `NS`, the spatial-axis cardinality from the
shape parameters of §4.3.  The discriminant
`trace² − 4 · det = 9 − 4 = 5` reads as `NS + NT`, the atomicity
sum.  And the eigenvalues `(3 ± √5) / 2 = φ², 1/φ²` carry the
golden ratio φ = (1 + √5) / 2 as the matrix's fixed point.

So the matrix is not an external encoding choice imposed on the
clauses.  It is what the clauses look like when written
algebraically.  The bridge theorem at
`lean/E213/Lib/Math/Algebra/Mobius213.lean` is ∅-axiom — the encoding is
derivable, not imposed.  The four clauses remain the minimum-
commitment statement; the Möbius form is their algebraic
*consequence*.

### Fibonacci at low order — the shape was not chosen

The shape parameters of §4.3 are `(NS, NT, d) = (3, 2, 5)`.
Read as a Fibonacci sequence, these are `(F₄, F₃, F₅)` —
three consecutive terms.  The relation `F_{k} = F_{k−1} + F_{k−2}`
gives `5 = 3 + 2`, which is the axiom's atomicity sum from above.

This is more than a numerical coincidence.  The `PairForcing.lean`
proof of §4.3 — which establishes that `(NS, NT) = (3, 2)` is
the unique admissible shape under arity = 2 and atomicity — does
not "select" these values; it identifies them as the unique
consecutive-Fibonacci pair compatible with the constraint.  The
logical direction runs the other way from a first reading: it is
not "we choose (3, 2) and notice Fibonacci"; it is **"Fibonacci
recurrence at low order leaves exactly this configuration
admissible, and the axiom is the residue of that admissibility."**

The Möbius matrix `P` is the Pell-Fibonacci generator; its
eigenvalues are φ² and 1/φ²; its iteration produces convergents
of the continued-fraction expansion of φ.  Each piece is the same
fact stated under a different reading.

### φ as the residue's quantitative measure

The fixed point φ has a stronger reading than "an eigenvalue
that happens to appear."  Iterating `P` from any starting point,
the *excess* over φ shrinks dyadically and the irreducible
residue converges to φ.  So φ is what is *left behind* when the
recursion of §1.2 has done as much erasure as it can.  It is the
algebraic embodiment of "the minimum residue — the minimum fixed
point of self-reference," and §5.6 unpacks the self-reference
side of this in detail.

The number is the same number across what one would initially
take to be unrelated domains.  In Cayley–Dickson algebra-tower
asymptotics, every base type's Moufang-failure rate converges as
`1 − (1/2) · (1/φ)^rank` — expressible exactly over Z[√5], with
no transcendental constants required.  In DRLT physics, the same
φ governs the CKM phase δ (as π/φ²), the Cabibbo angle's
Wolfenstein structure, and several neutrino mass ratios.  In
modular arithmetic, the same φ is the limit of consecutive-
Fibonacci ratios, with the modulus periodicity controlled by the
same matrix `P`.

None of these are reconciled coincidences.  They are the same
Lens result — the matrix's fixed point — read out across
domains.  This is the operational content of §1.5: when an act
of pointing succeeds, the residue is what is left, and any Lens
that reads the residue produces consistent output.  φ is what
that residue looks like under the algebra-Lens.

### The 1 on the off-diagonal — the glue

The Möbius matrix has 1's on both off-diagonals.  Read
arithmetically, this is `NS − NT = 1`: the difference between
the spatial- and temporal-axis cardinalities is unity.  Read
algebraically, this is the rotation invariant `det P = 1`.  Read
combinatorially, this is the fact that gcd(NS, NT) = 1 — the
two cardinalities are coprime, which is what makes the
Chinese-Remainder decomposition `ℤ / 6 ≅ ℤ / 2 × ℤ / 3` operative.

So the off-diagonal `1` is the **glue** between the two
cardinalities.  It is not an extra parameter; it is the difference
that allows the two to be distinct (NS ≠ NT) while remaining
coprime, which is in turn what makes the matrix's iteration
have a single fixed point rather than two attractors or none.
Without it the form falls apart in either direction (no
distinction, no recurrence).

### What the Möbius matrix is and is not

The matrix is not a structure layered above the axiom.  It is
what the axiom looks like when one asks "what algebraic object
is this?" — the answer it produces, not a substrate it sits on.
The four clauses remain the minimum commitment, and the matrix
is one of their canonical Lens outputs.

The matrix admits two simultaneous Lens readings, frozen and
dynamic, that §5.7 treats in detail.  In its frozen reading the
matrix points to φ as an attractor; in its dynamic reading its
iteration is the convergent trajectory.  An internal observer
cannot prefer one reading over the other, because the
preference would require an external time axis that the axiom
does not provide.

The same point shows up at a different scale in the parametric
`configCount : Nat → Nat` family
(`Lib/Math/Cohomology/Fractal/ConfigCount.lean`): it has multiple
routes to its level-2 value `5²⁵`, and the routes agree because
they read the same residue.  Cross-route agreement is the operational
signature of "no exterior" (§5.1), not a coincidence in need of
explanation.
