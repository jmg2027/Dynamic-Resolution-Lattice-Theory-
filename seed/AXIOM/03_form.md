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

- **One**: No object of distinction, so reference is impossible.
  Being something cannot be established.  Therefore disqualified.
- **Two**: Distinction is established for the first time.  Minimum
  satisfied.
- **Taking three or more as primitive**: the third something can be
  defined by its relation with the existing two, so there is no
  reason to treat it as primitive.  Unnecessary commitment.

- **Unary (operation on one)**: Self-reflexive and cannot produce a
  new something.
- **Binary**: The minimum form in which a new something arises from
  two somethings.  Necessary and sufficient.
- **Ternary or more**: Reconstructible by repetition of binary.  No
  reason to treat as primitive.

That is, **two + binary** is the unique minimum choice.

## §4.3 Why symmetric, why anti-reflexive

- **Symmetric**: No basis for assigning an absolute order.
  Distinguishing `a/b` from `b/a` silently imports an absolute
  criterion for which comes "first."
- **Anti-reflexive**: Pairing with oneself does not create an
  object of distinction (oneself is not distinguished from oneself).
  This directly conflicts with Axiom 1 (primitive distinction).

## §4.4 The (x+1) → (2x+1) iterator: Raw's natural form

The "two + binary" choice (§4.2) admits a uniform algebraic
expression as the iterator:

  x  →  (2x + 1) / (x + 1)

corresponding to the Möbius matrix `[[2, 1], [1, 1]]`.

  - "(x + 1)" — clause 2 (binary pairing of `x` with identity)
  - "(2x + 1)" — repeated pairing (binary applied twice with identity)
  - division — clause 1 (distinction between two paired forms)

This iterator captures the *minimal form* of repeated identity-
preserving binary pairing.  Its fixed point is

  x² − x − 1 = 0  →  x = (1 + √5)/2 = φ

where 5 = trace²−4·det = 9−4 = NS+NT (the atomicity sum, §3.4).

The choice "two + binary" therefore generates the φ-residue
algebraically, with no further commitment beyond the four clauses.
This is recorded as the bridge theorem:

  `lean/E213/Theory/Raw/Mobius.lean`

The form is *not assumed*; it is *induced* by the minimal axiom.
