# §4. Why this form was chosen

## §4.1 Austerity as audit

The axiom is intentionally austere.  The intent is **defensive**.

- The moment it is written in language, residual import is
  unavoidable, but its footprint can be minimized.
- If additional commitment slips in during derivation, **the
  contrast with the austere axiom immediately detects it as fudge**.
- The axiom itself serves as the contract for "can everything be
  derived from just this?"

Austerity is not poverty — it is **auditability**.

## §4.2 Why two, why binary

(Caveat: "two" throughout this section is the *count-Lens reading*
of distinguishing's residue, not a Raw cardinality commitment.
Cardinality at Raw is absent per `02_statement.md` §3.3.)

- **One**: Distinguishing cannot operate at all — no second
  something for the first to be distinguishable from.  Nothing is
  pointed at.
- **Two**: The minimum count-Lens reading of a successful
  distinguishing.  Not "two somethings prior to distinguishing":
  the count `2` *is* the residue of the first distinguishing
  operation.
- **Three or more as primitive**: a third something is the
  count-Lens reading of *further* distinguishing operations applied
  to the existing residue.  Treating count `≥ 3` as primitive
  imports cardinality where distinguishing has not yet produced
  that count.

- **Unary (operation on one)**: Self-reflexive and cannot produce a
  new something.
- **Binary**: The minimum form in which a new something arises from
  a residue with two-count.  Necessary and sufficient.
- **Ternary or more**: Reconstructible by repetition of binary.  No
  reason to treat as primitive.

That is, **two + binary** is the unique minimum *count-Lens shape*
of the Raw residue — not a chosen pair of numbers but the only
count-Lens reading the first distinguishing admits.

## §4.3 Why symmetric, why anti-reflexive

- **Symmetric**: No basis for assigning an absolute order.
  Distinguishing `a/b` from `b/a` silently imports an absolute
  criterion for which comes "first."
- **Anti-reflexive**: Pairing with oneself does not create an
  object of distinction (oneself is not distinguished from oneself).
  This directly conflicts with Axiom 1 (primitive distinction).

## §4.4 Algebraic signature (cross-ref)

The "two + binary" choice (§4.2) admits the Möbius iterator
`P(x) = (2x+1)/(x+1)` as natural form, fixed point φ = (1+√5)/2.
See `02_statement.md §3.4` for the algebraic signature
(`[[2,1],[1,1]]` matrix, trace 3 = NS, det 1, disc 5 = NS+NT,
eigenvalues φ², 1/φ²).  Bridge theorem: `lean/E213/Theory/Raw/
Mobius.lean`.  The form is *induced* by the minimum axiom, not
assumed.
