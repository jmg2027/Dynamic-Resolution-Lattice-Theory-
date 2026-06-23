# §2. The axiom

## §2.1 Language used

Writing the axiom requires three words.  Each carries residual
import; each is adopted as a **minimum-commitment expression,
with acknowledgement** of what it continues to drag in.

  - **Something** — a unit that can be pointed at.  The word is
    deliberately vague; tightening it would import structure
    that the axiom does not commit to.
  - **Distinction** — the confirmation of "not equal."  The word
    "difference" was rejected because it presupposes "sameness"
    as the default state.  "Distinction" is the minimum.
  - **Primitive** — no longer reducible.  The pledge that
    reduction stops here is part of the meaning of the word.

These three are enough.  Every other term used below is either
derived from them or marked explicitly as an encoding artefact.

---

## §2.2 The minimum-commitment statement

The 213 axiom is **the closure of "something exists" under
primitive distinction**.  As compactly as the language permits:

> Say `a` exists.  This very pointing already commits to the
> residue of the act — there is now "something distinguishable
> from `a`," call it `b`; and "the residue of distinguishing
> `a` from `b`," call it `a/b`; and "the residue of
> distinguishing `a` from `a/b`," call it `a/(a/b)`; and so
> on.
>
> The family of all such residues is what we call **Raw**.  That
> is the whole axiom.

A subtle point: `/` (slash) is **not an operator**.  "`a/b`
exists" is a *consequence* of "`a` exists," not the application
of some binary operation to `a` and `b`.  The slash is a way of
**referring** to a particular member of the residue family —
naming what was produced, not invoking a function.

A second subtlety: what looks like a recursion of notation in
the statement — first `b`, then `a/b`, then `a/(a/b)`, "and so
on" — is the **expository shadow of self-completion**, not a
temporal or inductive genesis.  Raw is not assembled in stages
that the statement is narrating.  The labels `a`, `b`, `a/b` are
the way a Lens reads the residue family after the fact (§6.1:
chart-local labels), not a mechanism inside the Raw structure.
§2.3 records the same point from the act's side: the pointing is
already complete.

---

## §2.3 Self-completion

The four clauses below are not steps in a construction.  When
pointing operates, all four are **simultaneously present**:
distinguishing yields a residue, the residue is itself a
something, the pairing is direction-free, and no self-pair
forms.  These are aspects of one event, not stages of a process.
The numbering is a notational convenience for the Lean encoding;
the act of pointing is already complete.

This is what §5.5 expands on: no partial pointing exists, no Raw
is "halfway formed" awaiting later Lens application to acquire
the rest of its structure.

---

## §2.4 Code-friendly four-clause restatement

For the Lean implementation, the axiom is restated as four
clauses.  Clauses 1 and 2 are the **positive** content; clauses 3
and 4 add **no positive commitment** — they record axiom-level
*absences* (no absolute order; no self-residue, §3.3), read off the
completed act, not bolted onto a machine.  What the Lean
type-theory codomain costs is the need to **declare** those absences
explicitly; how that declaration classifies under §10.3 differs by
clause — clause 4's `≠`-precondition is an **(α) re-expression of the
axiom**, while clause 3's symmetry is enforced by **(β)**
canonicalisation machinery with a **(γ)** symmetry law.  The full
cost catalogue is §10.

| # | Clause | Status |
|---|---|---|
| 1 | Distinguishing operates; the residue is recorded as distinguishable somethings `a`, `b`. | **axiom (positive)** — the re-expression of "a exists" together with its inevitable distinguishing residue.  The `2` here is the count-Lens reading of the result, not a Raw-level cardinality commitment; cardinality is absent at Raw per §2.5. |
| 2 | The residue of distinguishing already-distinguished somethings is itself a something: `a/b`. | **axiom (positive)** — the auto-emergence of the residue family.  `/` is *referring*, not operator. |
| 3 | Pairing is symmetric: `a/b = b/a`. | **axiom-level absence, declared** — no absolute order exists in the axiom (§3.3); Lean's inductive presentation imposes argument positions, so the absence is re-expressed as a canonical-form quotient: the **(β)** canonicalisation machinery (`Tree.cmp`, `Tree.canonical`) with the symmetry law `Raw.slash_comm` a **(γ)** consequence (§10.3). |
| 4 | No pairing with oneself: `x/x` is undefined. | **axiom-level absence, declared** — distinguishing has no self-operand (§3.3); Lean re-expresses this as the explicit precondition `x ≠ y` to block `slash x x` (α re-expression of clauses 1–2, §10.3). |

The forcing chain that explains *why* exactly these four clauses
— and not three, not five — is in §3.4.

---

## §2.5 What the axiom does not commit to

The list below is essential.  Every item is a candidate for
silent import during derivation.  To use any of them as a
result, one must first construct a Lens whose application
produces it; otherwise the derivation has smuggled in something
the axiom does not provide, and the Lens must be made explicit
or the derivation corrected.

  - **Size, cardinality, finiteness, infinity** — Lens output.
    "Two somethings" in §2.2 is the count-Lens reading of the
    first distinguishing, not a Raw-level cardinality
    statement.
  - **Order, hierarchy, ranking, sequence** — `Tree.cmp` in the
    Lean encoding is an encoding artefact (the canonical-form
    selector for the quotient), not an axiom commitment.
  - **Sets, element-of, membership** — set theory is foreign to
    the axiom and is never invoked silently.
  - **Operators, operations** — `/` is referring, not an
    operation; no function symbol is committed.
  - **Inductive structure** — the Lean inductive presentation
    imports ℕ, but ℕ is itself a Lens result of Raw, so
    importing it prior to Raw is an encoding cost (§10).
  - **Equality and its negation `≠`** — borrowed from Lean's
    metatheory to express clause 4.
  - **Observer, space, perception, structure, geometry** — none
    of these are operands of the axiom.
  - **Mode of existence** (already-present vs. being-generated)
    — the dichotomy itself is an import (§5.4).
  - **Algebraic laws** — associativity, distributivity,
    identity, inverse: none committed.

These absences are the contract.  If during derivation any of
them appears, the question is not "should it be allowed?" but
"which Lens produced it, and is the Lens choice acknowledged?"
