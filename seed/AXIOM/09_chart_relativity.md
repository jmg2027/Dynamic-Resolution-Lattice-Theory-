# §9. Chart relativity, flat ontology, and the emergence of structure

Companion note: `research-notes/2026-05-18_lens_emergence_path.md`
collects the long-form discussion.  This chapter records the
*principles* in axiom-corpus form, with cross-references rather than
re-derivation.

The four sections below are increasing in scope.  §9.1 and §9.2 are
direct readings of the existing axiom commitments.  §9.3 is the
flat-ontology framing — strict reading lives in `seed/RESOLUTION_
LIMIT_SPEC.md` and in the caveat below.  §9.4 is gestural and
flagged as conjecture pending a minimal prototype.

## §9.1 Raw.a and Raw.b are chart-local labels

The 213 axiom commits to two distinct primitive distinctions but
does *not* name them.  `Raw.a` and `Raw.b` in the Lean encoding are
*one chosen labelling*; under a different reference, two other
Raws would occupy the atom position and the current atoms would
themselves be a slash of (two deeper) Raws.

`inductive Tree | a | b | slash` therefore hardcodes one chart.
The chart-relativity statement — "any pair of distinct Raws can
serve as atoms" — is currently *implicit* in the axiom.  A
chart-invariance theorem (cf. Option D of the companion note,
§5) would make it explicit but has not been undertaken.

## §9.2 Operation and object are not pre-separated

Every Raw participates simultaneously as:

- an **object** — the result of slashing two prior Raws,
- an **operator-part** — an argument to the slash that builds
  some later Raw.

The `inductive Tree` shape forces a node/arrow separation that the
axiom does not impose.  This is a property *of the encoding*, not of
Raw.  The cost is catalogued in `08_encoding_costs.md` §8a.1 as the
inductive-type entry; this chapter adds the *operational* reading.

A self-referential cascade picture: for an internal observer to be
defined it requires another object; the boundary between the two is
itself an object; the boundary of that boundary is an object; and so
on.  A finite chart of this cascade is what we call Raw.  No
exterior is invoked — cf. `07_self_reference.md` §8.1.

## §9.3 Flat ontology — types, objects, relations share one universe

| Unit | Element | Predicate form |
|---|---|---|
| object (1st-order) | r ∈ Raw | Raw → Bool |
| object (n-th order) | (r₁,…,rₙ) ∈ Rawⁿ | Rawⁿ → Bool |
| type | a subset of Rawⁿ | predicate |
| relation | a subset of Raw² | predicate |
| function | a functional subset of Raw² | predicate + uniqueness |
| Lens | (labelled) predicate | (Raw → α, α Raw-encodable) |

One dimension — no separate universes for types, objects, relations.

**Strict ∅-axiom reading.**  Treating "predicate" as `Set Rawⁿ` (a
`Prop`-valued function) requires `propext` / `Classical` to do most
useful work, which the ∅-axiom standard forbids
(`seed/AXIOM/04_falsifiability.md` §5.2.1).  The strict reading
uses `Rawⁿ → Bool` (decidable predicates).  The table above is a
picture of the flat ontology; the formal translation runs through
decidable predicates only.  Self-referential closure
(predicates Raw-encoded) is realised in
`lean/E213/Lens/Cardinality/Godel.lean` under this strict reading.

## §9.4 Syntactic internalization (gestural)

Gödel encoding extends past **referent Raws** (`Raw.a`, `slash`,
…) to **notation glyphs** (`{`, `}`, `,`, `/`, whitespace, …) as
themselves Raw, with expressions becoming sequence-Raws of
glyph-Raws.  "Meaningless punctuation" then becomes external
convention rather than essence.

**L2 prototype**: `lean/E213/Lens/SyntacticInternalization.lean`.
7-glyph alphabet (`a`, `b`, `/`, `(`, `)`, `,`, whitespace) with
each glyph mapped to a distinct Raw via the Method A chain
(`Glyph.toRaw : Glyph → Raw`).  Injectivity proved by kernel
evaluation (`Glyph.toRaw_injective`).  4 strict ∅-axiom symbols.

The cascade halts at L2: writing the encoding requires only the
same 7 glyphs, themselves Raw-encoded.  No L3 meta-meta-glyph
alphabet is needed.

**Out of scope (L3+ work).**  A full parser/printer round-trip
(Raw ↔ glyph-sequence) and a Raw-internal `IsExpressionEncoding`
predicate are deferred.  The L2 prototype establishes the
*glyph-symbol-as-Raw* level; richer L3 work — where the
arrangement of glyphs is itself Raw-encoded constructively — is
future development.

## Reading order

- `02_statement.md` §3.3 (what the axiom does *not* commit to —
  including size, cardinality, observer) is the prerequisite.
- `08_encoding_costs.md` lists the costs *of* the Lean
  implementation; this chapter is the dual reading — what those
  costs *imply* about chart vs. essence.
- `07_self_reference.md` §8.1 closes the circle: no exterior, so
  the cascade is internal.

## What this chapter is not

- It is not a new commitment of the axiom.  The four sections
  re-read existing commitments with a new vocabulary.
- It is not a falsifier (`04_falsifiability.md` §5.2.2).  No
  measurable proposition is added.
- It is not a precision result.  See `STRICT_ZERO_AXIOM.md` for the
  ∅-axiom catalog; this chapter contributes 0 PURE theorems.
