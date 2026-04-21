# 00 — The thesis (Mingu Jeong, 2026-04-21)

Recorded verbatim-in-spirit from the session transcript; this
is the *originator's* framing, not Claude's.

## The core claim

The Raw axiom is **purely syntactic-finite** (three
clauses, three constructors).  It makes **no cardinality
postulate**.  From the axiom alone, it is undefined whether
Raw is finite or infinite — the question has no answer
without a Lens.

Different Lens choices yield different cardinality
phenomena on the *same* Raw: one Lens gives a countable
image, another gives uncountable.  "Infinity" is therefore
**a Lens output**, not a Raw primitive.

## The analogy

Mathematicians routinely handle infinity through finite
formal means (induction schemes, compactness, recursive
syntax).  Raw does the same at the foundation level:
finite generation rule, yet through Lens all infinities
(and hyper-infinities) are observable.

## The provability intuition

The generating system is finite; the observations through
Lens can be arbitrarily large.  This duality — finite
generation vs unbounded Lens-visible phenomena — is
claimed to be **formally provable**.

## Two somethings as primitive distinction

The justification for Raw being enough: in a space where
nothing is absolute, distinction requires two things.  Two
*relational objects* (관계객체 / 원시적 구분객체) form
the minimal and unique substrate for "knowing" anything.
Raw is built on exactly this.

## On the diagonal-completeness sketch

(Partially ambiguous in the originator's mind; recorded as
initial intuition.)  Three Raw objects generate a countable
chain; a diagonal-3 generates another; Cantor-diagonal
between the two yields completeness.  Taken as a
heuristic hypothesis, not a proof.  Whether it works
exactly, "the emulator will show" — i.e. leave it to
Lean formalisation.

## On Lean's role

Lean is **hardware for emulating Raw**.  Its type theory
is not foundational to Raw; Raw is prior to Lean.  Lean's
role is to provide mechanical check that the Raw-side
construction behaves as claimed.  The choice of
Mathlib-free core is not aesthetic — it prevents
smuggling external math into Raw's supposed
self-containedness.
