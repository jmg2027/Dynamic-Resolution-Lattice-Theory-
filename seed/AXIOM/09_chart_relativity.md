# §9. Chart relativity, flat ontology, and the emergence of structure

Companion note: `research-notes/2026-05-18_lens_emergence_path.md`
collects the long-form discussion.  This chapter records the
*principles* in axiom-corpus form, with cross-references rather than
re-derivation.

The four sections below are increasing in scope.  §9.1 and §9.2 are
direct readings of the existing axiom commitments; §9.1's
chart-relativity now has explicit proof in
`Lens/Number/Nat213/ChartGeneral`.  §9.3 is the flat-ontology
framing — strict reading lives in `seed/RESOLUTION_LIMIT_SPEC.md`
and in the caveat below.  §9.4 was the gestural conjecture; it now
has a full L2 + L3 realisation in `Lens/SyntacticInternalization`
(7-glyph alphabet + Polish-prefix universal round-trip
`∀ t, parseTree (printTree t) = some t`).

## §9.1 Raw.a and Raw.b are chart-local labels

The 213 axiom commits to two distinct primitive distinctions but
does *not* name them.  `Raw.a` and `Raw.b` in the Lean encoding are
*one chosen labelling*; under a different reference, two other
Raws would occupy the atom position and the current atoms would
themselves be a slash of (two deeper) Raws.

`inductive Tree | a | b | slash` therefore hardcodes one chart.
The chart-relativity statement — "any pair of distinct Raws can
serve as atoms" — was originally implicit in the axiom and has
since been made **explicit** in
`lean/E213/Lens/Number/Nat213/ChartGeneral.lean`
(Option D of the companion note, §5).  The file parameterises
Method A over any `(r₀, r')` with `r₀ ≠ r'` and proves the
chart-invariance theorem
`value (chartChain r₀ r' h n) = value r₀ + n * value r'`.

## §9.2 Operation and object are not pre-separated

What the Lean encoding labels as **object** (the result of slashing
two prior Raws) and **operator-part** (an argument to a slash that
builds some later Raw) are not two roles a Raw simultaneously
*occupies* — they are two Lens readings of the same Raw event.  The
Raw does not host two roles; the labelling hosts two readings.

The `inductive Tree` shape forces a node/arrow separation that the
axiom does not impose.  This separation lives in the *labelling*,
not in Raw.  The cost is catalogued in `08_encoding_costs.md`
§8a.1 as the inductive-type entry; this chapter adds the
*operational* reading: state-transition = state, operator = object
are the natural form of a system with no external time axis or
external role-assigner.

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

## §9.4 Syntactic internalization

Gödel encoding extends past **referent Raws** (`Raw.a`, `slash`,
…) to **notation glyphs** (`{`, `}`, `,`, `/`, whitespace, …) as
themselves Raw, with expressions becoming sequence-Raws of
glyph-Raws.  "Meaningless punctuation" then becomes external
convention rather than essence.

**Full L2 + L3 + L4 realisation**:
`lean/E213/Lens/SyntacticInternalization.lean` (25 strict ∅-axiom
symbols).

L2 (cascade halts at glyph encoding):
  - `Glyph` inductive with 7 constructors (`a`, `b`, `/`, `(`,
    `)`, `,`, whitespace).
  - `Glyph.toRaw : Glyph → Raw` maps to 7 distinct Method A
    numerals.
  - `Glyph.toRaw_injective` — kernel-decided.

L3 (full universal round-trip):
  - `printTree : Tree → List Glyph` — Polish-prefix encoding.
  - `printRaw : Raw → List Glyph` — lifted via `.val`.
  - `parseHelper : Nat → List Glyph → Option (Tree × List Glyph)`
    — fuel-bounded constructive parser.
  - `parseTree : List Glyph → Option Tree` — top-level parser
    with fuel = list length.
  - `parseHelper_fuel_succ`, `parseHelper_fuel_mono` — fuel
    monotonicity.
  - `parseHelper_printTree_append` — exact-size correctness.
  - `printTree_length_ge_size` — length-vs-size inequality.
  - **`parseTree_printTree : ∀ t, parseTree (printTree t) = some t`** —
    the universal round-trip theorem.
  - `parseTree_printRaw` — Raw-level corollary.

L4 (bijection closure, 2026-05-18):
  - `parseHelper_sound` — soundness: any successful parse
    `parseHelper n gs = some (t, rest)` proves
    `gs = printTree t ++ rest` (consumed prefix is exactly the
    print of the returned tree).
  - **`printTree_parseTree : parseTree gs = some t → printTree t = gs`**
    — reverse round-trip / lossless parser.
  - `printTree_injective` — corollary of `parseTree_printTree`.
  - `printRaw_parseTree` — Raw-level corollary.

Together L3 + L4 establish a bijection between `Tree` and
`Range(printTree)`: `printTree` is injective with `parseTree` as
its left inverse on the image.

All Nat / List arithmetic uses Lean 4 core lemmas or the
∅-axiom utility `E213.Tactic.List213.{append_nil, append_assoc,
length_append, length_append_rev, length_map}` (promoted to
`Meta/Tactic/List213.lean` 2026-05-17).  The standard
`List.append_assoc`, `List.append_nil`, `List.length_append`
carry `propext` and would corrupt the strict-∅ contract; the
List213 versions are `congrArg`-based replacements.

The §9.4 cascade halts at L2: writing the encoding (this very
file) uses only the same 7 glyphs.  L3 closes the loop with
constructive parser/printer round-trip.

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
