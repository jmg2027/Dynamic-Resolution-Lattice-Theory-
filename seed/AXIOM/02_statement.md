# §3. Axiom statement

## §3.1 Declaration on the language used

To write this axiom in text, the following are used.  Each carries a
residual import, and is used because no better expression yet exists.
They are adopted as minimum-commitment expressions **with
acknowledgment** of the residual import.

- **"Something"** — a unit that can be pointed at.  Any choice among
  "thing," "entity," "term," etc. carries import.
- **"Distinction"** — the confirmation of "not being equal."
  "Difference" is avoided since it presupposes "sameness."
  "Distinction" is currently the minimum.
- **"Primitive"** — no longer reducible further.  A pledge not to
  attempt further decomposition.

## §3.2 The axiom

1. **Something exists.**  At least two.  These are recorded as `a`,
   `b` for convenience.  `a` and `b` stand in a **primitive
   distinction** relation — i.e., no relation other than "not equal"
   is presupposed between the two.

2. **The pairing of two somethings is yet another something.**  The
   pairing of `a`, `b` is recorded as `a / b` for convenience.
   `a / b` is a new element of Raw and can be paired again with other
   Raw elements.

3. **Pairing is symmetric.**  `a / b` and `b / a` are the same Raw
   element.  There is no absolute order for which comes "first."

4. **There is no pairing with oneself.**  For any Raw element `x`,
   `x / x` is undefined.  Oneself is not distinguished from oneself,
   so it cannot be an object of primitive distinction.

## §3.3 What is **absent** from the axiom

Things **not** contained in the axiom — to use any of these as
results of the axiom, a separate Lens derivation is required.

- Size / cardinality / finiteness / infinity.
- Order / hierarchy / ranking.
- Set / element relation / membership.
- Observer / space / perception / structure / geometry.
- Mode of existence (already present vs. being generated).
- Algebraic laws: associativity, distributivity, identity element,
  inverse, etc.

If any of these appears during derivation, it is **the result of
applying a specific Lens**, not the axiom itself.  Which Lens it came
from must be made explicit.

## §3.4 Algebraic signature — Möbius interpretation (∅-axiom theorem)

The 4-clause axiom admits a compact algebraic encoding as the
Möbius matrix `[[2, 1], [1, 1]]`:

  - "2" — clause 1 (two somethings `a`, `b`)
  - "1" — clause 4 (no self-pairing = identity preservation, det = 1)
  - "3" — trace = 2 + 1 (the spatial dimension `NS`)
  - disc = trace² − 4·det = 9 − 4 = **5 = NS + NT** (atomicity sum)
  - eigenvalues = `(3 ± √5)/2` = `φ²`, `1/φ²`

This is an *interpretation*, not an addition to the axiom.  The
axiom remains minimum-commitment; the Möbius reading is a
∅-axiom-derived bridge theorem at:

  - `lean/E213/Theory/Raw/Mobius.lean` (P_numerator, P_denominator,
    discriminant, trace, det)

The Möbius P(x) = (2x+1)/(x+1) iterator is the *natural form* of
Raw's binary slash applied with identity preservation:

```
slash x identity         ←→  x + 1
slash (slash x x) ident  ←→  2x + 1
```

The fixed point of P is the golden ratio φ = (1+√5)/2, identified
with the residue of self-pointing iteration (cf. G29_residue,
G57_213_mobius_signature).

The same φ appears in DRLT physics (CKM phase δ = π/φ², Cabibbo
Wolfenstein A = φ/c, neutrino mass ratios) and in the algebra
tower asymptote (1 − 0.5/φ^rank).  Cross-domain consistency.

**This is not a modification to the axiom.** The 4 clauses in
§3.2 remain the minimum-commitment statement; §3.4 records an
algebraic *consequence* expressible as a Theory-level theorem.
