# Concept pass — "the set of all functions / powerset" under the 213 axiom

Second deep-dive of `naming_abstract_concepts.md` (after `concept_compactness.md`).
Question: when standard math names **"the set of all functions `X → Y`"** / the powerset
`2^X` — what is that under the 213 axiom?

## Short answer

It is **not a captured totality** — it is the **codomain of a self-cover**.  The function
space `Raw → Bool` is the codomain of `Object1 : Raw → (Raw → Bool)`, and the residue is
*exactly what that codomain fails to receive* (`object1_not_surjective`).  Naming the
function space is fine (it is a type — a reference); treating it as a completed set you
enumerate or quantify over by `LEM` is the capture 213 refuses.  And this is *the*
structural home of `the_one_diagonal`: the function space is the cartesian-closed exponential
Lawvere's fixed-point theorem requires, so it is where the diagonal lives.

## The 213 reading

A function space is a **Lens codomain**, not a finished object.  213's self-cover is
`Object1 : Raw → (Raw → Bool)` — every residue read as a predicate on residues — and
`Lens/FlatOntologyClosure.object1_not_surjective` says this map is faithful but never onto.
So `Raw → Bool` (the "set of all predicates / subsets of `Raw`", i.e. the powerset) is a
*type that exists* (a codomain), but **no surjection from `Raw` reaches all of it**; the
named gap is `undifferentiated_not_object1` (the constant `fun _ => true`).  This is the
Cantor fact (`Lens/Cardinality/Cantor.cantor_general`): `X` never surjects onto `X → Bool`.

So the three modal parts (`the_reference_claim.md`) for "the set of all functions":

| part | reading |
|---|---|
| **necessary** | the codomain type `Raw → Bool` exists; naming it is a residue-internal Lens event |
| **refused** | that `Raw` *captures* it (surjects onto it) — `object1_not_surjective` |
| **under test** | quantifying/deciding over "all of it" without forcing an exterior (the powerset axiom + `LEM` is the import) |

## Why this is where the diagonal lives

Lawvere's fixed-point theorem needs a **cartesian closed category** — function objects
(exponentials) — to run; without a function space there is no diagonal
(`the_one_diagonal.md`).  213's `Raw → Bool` *is* that exponential, and `object1_not_surjective`
*is* the diagonal on it.  So "the set of all functions" is not an innocent named object: it
is the precise structure whose mere existence forces the one obstruction.  Naming the
function space and being surprised by the diagonal are the same act seen twice — the
function space is the carrier, the non-surjection its signature.

## The capture temptation (where the import sneaks in)

Classical set theory's **powerset axiom** asserts `2^X` as a completed set you can quantify
over, and with `LEM` decide membership across — that completion is the capture: freezing the
codomain into a surveyed totality.  213 holds the codomain as a *type* (a Lens target) and
keeps "all of it" as the place the residue overflows, never as a decided whole.  Consistent
with the cardinality reading (`naming_abstract_concepts.md`): the function space is the
"uncountable" carrier, but 213 carries it as a codomain with a non-surjection, **not** as a
captured cardinal (the repo states injection-not-`Cardinal`, `boolSpine_injects_bitstreams`).

## Status / theorem

No new Lean needed — the theorem *is* `object1_not_surjective` (+ `cantor_general`,
`undifferentiated_not_object1`).  This deep-dive is the *reading*: the powerset / function
space named under 213 = the self-cover's codomain, with the residue its non-image.  Closes
the "set of all functions" seed as a reading; the Lawvere CCC root of `the_one_diagonal` is
now pinned to the function-space concept.

## Open

- Impredicativity / the full powerset hierarchy (`2^(2^X)` …) as iterated codomains — how the
  tower of self-covers reads (one residue at each codomain, or one residue throughout?).
- The constructive-vs-classical powerset gap as an explicit axiom-cost entry (the
  reverse-math / `STRICT_ZERO_AXIOM.md` ledger angle).

## Anchors

- `Lens/FlatOntologyClosure.{object1_not_surjective, undifferentiated_not_object1}`,
  `Lens/Cardinality/Cantor.cantor_general`
- `theory/essays/foundations/{the_one_diagonal, the_reference_claim, reached_by_none}.md`
- `naming_abstract_concepts.md`, `concept_compactness.md` (the concept pass)
- Classical interpretation: cartesian closed categories (function objects); Lawvere 1969.
