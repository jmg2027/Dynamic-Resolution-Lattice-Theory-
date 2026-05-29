# §9. The Lean correspondence

The axiom of §2 is realised in Lean.  This chapter records how —
which files carry which content, what the mapping promises, and
where the audit trail lives.  The implementation costs that the
mapping incurs are catalogued separately in §10.

## §9.1 The faithful emulator

The current Raw implementation lives under `lean/E213/Theory/`:
two elements `a`, `b`, a binary `slash` with anti-reflexive and
commutative laws.  It is a faithful machine representation of
the axiom — faithful in the technical sense of §10.3, which
classifies every implementation device as either a re-expression
of the axiom (α), an encoding cost (β), an automatic
consequence (γ), or an additional commitment (δ), and exhibits
zero items in category δ.

The device-by-device classification and the cross-check with
the axiom is recorded at `lean/E213/AUDIT.md`.

A practical encoding note.  Lean 4 core has no primitive
quotient.  Raw is therefore implemented as a subtype
`{t : Tree // t.canonical = true}`, with the canonical
predicate selecting one representative per equivalence class.
The internal `Tree.cmp` (a total ordering on `Tree`) is an
**encoding artefact** used by the canonical-form selector — not
an axiom commitment.  The axiom contains no order whatsoever.
cmp-independence — the mathematical fact that the choice of
`Tree.cmp` has no observable effect on Theory — is mechanically
verified at `lean/E213/Theory/RawCmpIndependence.lean`.  The
full cost catalogue is §10.

Some derivations follow automatically from the axiom plus its
Lean encoding, with no additional commitment.  Three to flag
explicitly:

  - `Raw.swap` — the `a ↔ b` automorphism.  The first
    derivation from clause 1: "`a` and `b` have no relation
    other than not being equal" means swapping them must be an
    automorphism.
  - `Raw.fold` — the catamorphism.  The standard eliminator
    wrapper of an inductive type, and the tool for constructing
    every Lens.
  - The forced-shape proofs of §4.3 under `Theory/Atomicity/`.
    These are pure-ℕ propositions that do not import Raw; they
    state what Raw must look like.  They sit in `Theory/`
    structurally — as part of "what Raw must look like" — but
    their dependency on Raw is zero.

A small concession.  The `Theory/` ring currently hosts some
Lens-flavoured observables that, by strict layering, would
belong one ring out: `Raw.depth` in `Theory/Raw/Slash.lean`,
`Raw.leaves` in `Theory/Raw/Levels.lean`,
`Raw.fold_signed_swap` and `Raw.fold_swap_hom` in
`Theory/Raw/FoldSwap.lean`.  These are classified as an
**intentional convenience leak**: every Lens consumer
eventually needs these pure-induction theorems on `Tree`, and
relocating them gains nothing for axiom-minimality.

---

## §9.2 Three-direction uniqueness, bundled

The three readings of axiom uniqueness from §4 are bundled into
a single Lean statement at
`lean/E213/Meta/ThreeDirectionUniqueness.lean`:

  - **From below** — `Meta/AxiomMinimality.lean` and its
    capstone (§4.1).  No clause can be removed.
  - **Sideways** — the witness family
    `Lens/Universal/Witnesses/{Core, Nat2, Nat2Inj, Q213,
    Q213Inj, Nat3, Q213_3, TripleCapstone, Padding,
    PaddingCapstone}` (§4.2).  Any distinguishability framework
    factors through Raw.
  - **From above** — the cluster `Theory/Atomicity/{Five,
    PairForcing, NonDecomposable, Alive, ArityForcing,
    ArityForcingGeneral, PrimitiveSizes}` (§4.3).  Only one
    shape is self-consistent.

The bundling theorem certifies all three simultaneously.

---

## §9.3 Realisations of the doctrinal chapters

§5 (no exterior) and §6 (Lens readings) are doctrinal chapters;
both have concrete Lean realisations.

For §6:

  - `lean/E213/Lens/Number/Nat213/ChartGeneral.lean` — the §6.1
    chart-invariance theorem.  Method A parameterised over any
    pair `(r₀, r')` of distinct Raws.
  - `lean/E213/Lens/SyntacticInternalization.lean` — the §6.4
    full L2 + L3 + L4 realisation: seven-glyph alphabet,
    Polish-prefix printer and parser, universal round-trip.
  - `lean/E213/Lens/FlatOntology.lean` — the §6.3 forward
    direction (objects, types, relations, functions, Lenses all
    as decidable predicates on `Rawⁿ`).
  - `lean/E213/Lens/PredicateSelfEncoding.lean` — the §6.3
    closure direction (predicates encoded back to Raw via
    positional Gödel numbering).
  - `lean/E213/Lens/RawTopology.lean` — the §6.5 K_∞ ≡ point
    bookend: the constant-Lens collapse plus the
    four-property witness `k_infty_at_raw_bundle`.

For §5:

  - `lean/E213/Lib/Math/Mobius213.lean` — §3.5, §5.6, §5.7
    realisations of the Möbius matrix `[[2, 1], [1, 1]]`:
    Pell-unit invariants, characteristic polynomial, the
    frozen + dynamic dual reading.
  - `lean/E213/Meta/AxiomMinimality.lean` and its capstone —
    §2.4 and §3.4: the clause-minimality witnesses and the
    positive forcing chain.

---

## §9.4 Corpus boundary

The directory `seed/AXIOM/` is the **sole** axiom corpus.
Derivation work belongs in `research-notes/` (active scratch)
and in the Lean metatheory layer (`Meta/UniversalLens/`).
Active narratives live in `theory/THEORY_BOOK.md` (single
linearised reading path) and in per-area chapters at
`theory/<math, physics, lens, meta>/`.

---

## §9.5 Concrete numerics — Lens output or forced

Every concrete numeric in the current Lean tree falls into one
of two categories:

  - A **Lens construction** — produced by applying a specific
    Lens to Raw, with the Lens choice recorded in the Lean
    code.  `1/α_em = 137.036` is in this category.
  - A **forced-uniqueness theorem** under `Theory/Atomicity/` —
    the shape parameters `d = 5`, `NS = 3`, `NT = 2`, which §4.3
    proves to be the unique self-consistent fixed point.

External `eval`-style substitution that would import any of the
prohibited items from §2.5 (size, order, set membership,
operations, …) as fudge is mechanically prevented by the
falsifiability contract of §8.2.  If a numeric appears that
fits neither category, either the Lens is missing — name it —
or the theory is wrong.
