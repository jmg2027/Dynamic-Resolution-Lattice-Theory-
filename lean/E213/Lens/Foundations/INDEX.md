# `Lens/Foundations/` — the distinguishing as foundation

The corpus that establishes the **act of distinguishing** as the one
self-grounding primitive and the **residue** as its forced remainder
(`distinguishing_always_leaves_residue`).  Narrative: `theory/essays/
foundations/raw_and_lens_explained.md` (reader's guide) and
`theory/essays/foundations/the_distinguishing_is_the_primitive.md`.

## Files (9)

  - `Initiality.lean` — initiality of the Lens category
    (`Lens.view_unique`): fixing the atom- and combine-readings forces
    the whole reading.
  - `SemanticAtom.lean` — semantic-atom characterisation; **`raw_initial`**
    — the universal property: `Raw` is the initial distinguishing-structure
    over the total-combine `HasDistinguishing` category (∅-axiom existence
    + uniqueness).  *(Sealed-DIRTY by design on the Prop-side `combine_sym`
    field — propext; the Bool-lens content is PURE.)*
  - `FlatOntology.lean` — flat-ontology realisation: objects, types,
    relations, functions, and Lens all as decidable predicates on `Raw^n`
    (`Object1` self-cover).
  - `FlatOntologyClosure.lean` — `distinguishing_always_leaves_residue`
    (faithful + never-total self-cover): the residue is a **theorem**,
    `object1_not_surjective` (Cantor-diagonal on `Object1`).
  - `ResidueReentry.lean` — the residue re-enters; the cover never closes.
  - `NoExteriorClosure.lean` — naming is internal; distinguishing is
    downstream of no exterior.
  - `OneDiagonal.lean` — one Lawvere fixed point generates Cantor /
    Russell / Liar / Tarski **and** the residue: the residue is the
    *engine* of the limitative theorems, not a by-product.
  - `UniversalDistinguishing.lean` — the `DStr` schema: the distinguishing
    as a *classifier* (rivals are instances ≅ `Raw`, or fail a named clause
    D1–D6).  Uniqueness proven; the existence leg (injective catamorphism)
    is open partial-algebra engineering, no axiom needed.
  - `PredicateSelfEncoding.lean` — closure of predicate ↔ `Raw`: every
    finite-prefix / definable predicate is itself a `Raw` (positional
    truth-table Gödel numbering), closing the self-reference loop.

## Reading order (for newcomers, incl. AI)

`../LensCore` (what a Lens is) → `SemanticAtom.raw_initial` (the universal
property, *already proven*) → `FlatOntologyClosure` (the residue) →
`OneDiagonal` (residue = engine of the diagonal theorems) →
`../Number/Nat213/Generation` (number from the distinguishing) →
`UniversalDistinguishing` (the schema / rival-exclusion).

## Companion narrative

  · `theory/essays/foundations/raw_and_lens_explained.md`
  · `theory/essays/foundations/the_distinguishing_is_the_primitive.md`
  · `theory/essays/synthesis/forced_by_the_distinguishing.md`
  · `seed/AXIOM/01_residue.md` (the residue, foundational anchor)
