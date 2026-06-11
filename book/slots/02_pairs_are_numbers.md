# 2 · Pairs are numbers

## The tuple is the number

`a + x = b` with no answer on the list: classical mathematics says
"adjoin the negatives", manufactures a new kind of object, and writes
`x = b − a`.  This volume does neither.  The pair `(a, b)` — the
question's own data — **is** the number.  Nothing is adjoined; an
address in slot space is occupied.

Take this literally, because everything depends on it:

* `(1,3)` is a **two-axis number**.  It is not "a notation for 2".
* `(1,3)` and `(2,4)` are *related* — the cross-equation
  `1 + 4 = 2 + 3` holds (`Int213.subNatNat_eq_iff` gives the general
  form: `subNatNat A B = subNatNat C D ↔ A + D = C + B`) — but they
  are **not equal**.  Different points, one orbit.
* A Gaussian-type number with ℕ-components is `(p, q)`; with
  ℤ-components it is `((p₁,p₂),(q₁,q₂))`; with ℚ-components, four
  pairs.  **The nesting is the axis structure**, and the names
  "integer", "rational", "complex" are bookkeeping for the
  *operation-history of the axes* — not kinds of number.

## Reduction is a theorem, not an identity

Of course `(1,3)` and `(2,4)` can be "reduced to 2".  But notice what
that sentence actually contains: a *theorem* (every orbit of the
relation touches a distinguished point — for ×-pairs this is the
Euclid chain, `Gcd213.gcd_strip_coprime` and
`coprime_repr_unique`) and a *choice* (to name the orbit by that
point).  The theorem is mathematics; the choice is a **flattening
Lens** — one reading among several, never the default.  Apply it
reflexively and the axis structure your decorations carried —
the very thing that made `(1,3)` a two-axis number — is silently
destroyed.  The interesting question was never "what is the reduced
form" but "**why is reduction possible at all**", and that question
has a theorem for an answer.

## What classical notation hides

The same flattening hides inside notation:

* **`p + qi`**: the `+` here is *not* the list's `+`.  It is the
  axis-combination of a new operation — the pair arithmetic that the
  keystones define (`Int213.subNatNat_add_subNatNat`,
  `GaussTuple.gmul`).  Reusing the symbol smears two different
  operations into one glyph and lets the tupling pass unnoticed.
* **The fraction bar**: `3/6 = 1/2` asserts an *identity* where there
  is a *relation* between two ratio-pairs
  (`RatioLensFounding.ratioEquiv`).
* **`2 mod 2 = 0`**: the canonical remainder is the flattening
  readout of the wrap world — the least point of an arithmetic
  progression.  `2 mod 2` *is the class of `2`*; that it relates to
  `0` is a fact about the relation, not about what `2` is.

In slot form nothing is hidden: components stay separate, operations
on tuples are visibly new operations, and every "simplification" is
an explicit, optional act.

## Why this is also why the proofs carry no axioms

The discipline that follows from the ontology — hypotheses in
**witness form** (`a = c + e`, never `a − c`; `a = g·a₁`, never
`a/g`), total operations only — is precisely the discipline under
which every theorem in this volume checks with the **empty axiom
set**.  Partial operations smuggle in case distinctions that demand
classical choice; quotient types demand `Quot.sound`; the
subtraction sign demands `propext`-bearing library lemmas.  Refuse
them all and there is no seam for an axiom to enter.  "Looks cleaner"
and "proves with nothing" turn out to be the same decision.
