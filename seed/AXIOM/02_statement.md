# §3. Axiom statement

## §3.1 Declaration on the language used

To write this axiom in text, the following are used.  Each carries a
residual import, and is used because no better expression yet exists.
They are adopted as minimum-commitment expressions **with
acknowledgment** of the residual import.

- **"Something"** — a unit that can be pointed at.
- **"Distinction"** — the confirmation of "not being equal."
  "Difference" presupposes "sameness"; "distinction" is the minimum.
- **"Primitive"** — no longer reducible further.

## §3.2 The axiom — minimum-commitment statement

The 213 axiom is **the closure of "something exists" under primitive
distinction**.  In minimum-commitment language:

> **"a (exists)"** — and this very pointing automatically commits to
> the residue: "something distinguishable from a" (= b), "the residue
> of distinguishing a and b" (= a/b), "the residue of distinguishing
> a and a/b" (= a/(a/b)), …
>
> The family of all such residues is what we call **Raw**.  That is
> the whole axiom.

In particular: `/` (slash) is **not an operator**.  "a/b exists" is a
*consequence* of "a exists", not "the application of slash on a, b".
The slash is a **referring** — a way of pointing to a particular
member of the residue family.

### Self-completion

The four clauses below are not sequential additions.  When pointing
operates, all four are simultaneously present — distinguishing
yields a residue, the residue is itself a something, the pairing is
direction-free, no self-pair forms.  These are aspects of one
event, not steps in a construction.  The numbering is a notational
convenience for the Lean encoding; the act of pointing is already
complete.

### Code-friendly 4-clause restatement (with cost markers)

For Lean implementation, the axiom is restated as 4 clauses.  Clauses
3 and 4 are NOT in the axiom proper — they are imposed by the **Lean
type-theory codomain** as encoding costs (no order, no self-residue
in the axiom).  Details: `seed/AXIOM/08_encoding_costs.md`.

| # | Clause | Status |
|---|---|---|
| 1 | Distinguishing operates; the residue is recorded as distinguishable somethings `a`, `b`. | **axiom** (re-expression of "a exists" with its inevitable distinguishing residue — `2` is the count-Lens reading of the result, not a Raw cardinality commitment; cardinality is absent at Raw per §3.3) |
| 2 | The residue of distinguishing already-distinguished somethings is itself a something. `a/b`. | **axiom** (auto-emergence of the residue family — `/` is *referring*, not operator) |
| 3 | Pairing is symmetric: `a/b = b/a`. | **encoding cost** (order is absent from the axiom; Lean's inductive imposes argument positions, so symmetry must be declared as quotient) |
| 4 | No pairing with oneself: `x/x` undefined. | **encoding cost** (the concept "self-residue" is absent from the axiom; Lean must declare the precondition `x ≠ y` explicitly to block `slash x x`) |

## §3.3 What is **absent** from the axiom

Things **not** contained in the axiom.  To use any of these as
results, a separate Lens derivation is required.  If any appears
during derivation, it is **the result of applying a specific Lens**
— which Lens must be made explicit.

- **Size / cardinality / finiteness / infinity** — Lens output.
- **Order / hierarchy / ranking / sequence** — `Tree.cmp` in Lean is
  encoding artifact, not axiom.
- **Set / element relation / membership** — set theory is foreign.
- **Operator / operation** — `/` is referring, not an operation.
- **Inductive structure** — induction principle imports ℕ from Lean's
  type theory; ℕ is itself a Lens result, so importing it priorly is
  an encoding cost (`08_encoding_costs.md`).
- **Equality and its negation `≠`** — borrowed from Lean's metatheory.
- **Observer / space / perception / structure / geometry**.
- **Mode of existence** (already-present vs. being-generated).
- **Algebraic laws**: associativity, distributivity, identity,
  inverse, etc.

## §3.4 Algebraic signature — Möbius interpretation

The 4-clause restatement (§3.2 code-friendly form) admits a compact
algebraic encoding as the Möbius matrix `[[2, 1], [1, 1]]`:

  - "2" — two somethings `a`, `b`
  - "1" — identity preservation (det = 1)
  - "3" — trace = 2 + 1 (the spatial dimension `NS`)
  - disc = trace² − 4·det = 9 − 4 = **5 = NS + NT** (atomicity sum)
  - eigenvalues = `(3 ± √5)/2` = `φ²`, `1/φ²`

The Möbius iterator `P(x) = (2x+1)/(x+1)` is the natural form of the
"two + binary" choice.  Fixed point φ = (1+√5)/2 = the residue of
self-pointing iteration (cf. G29_residue, G57_213_mobius_signature).

The same φ appears in DRLT physics (CKM δ, Cabibbo, ν mass ratios)
and in the algebra tower asymptote — cross-domain consistency.

**Note**: this is an *interpretation*, not an addition.  Bridge
theorem at `lean/E213/Lib/Math/Mobius213.lean`.  The 4 clauses in
§3.2 remain the minimum-commitment statement; §3.4 records an
algebraic *consequence* (∅-axiom theorem).

**Dual reading** (frozen + dynamic).  The same matrix admits two
Lens readings on the same residue:
  - *Frozen*: φ is the unique fixed point of P (the attractor as
    static configuration).
  - *Dynamic*: P^n(x) → φ for any starting x (the iteration as
    trajectory).
Both readings hold simultaneously for an internal observer —
absent an external time axis to compare them under, the dichotomy
"frozen or dynamic?" is not posed.  Cf. `RESOLUTION_LIMIT_SPEC.md`
§2 (G120 Round 3 rewrite) for the parametric `configCount` family
where the same family value `5²⁵` is read via different routes —
family-evaluation-as-content principle.
