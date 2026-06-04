# §4. Three-direction uniqueness

The axiom of §2 is unique in three independent senses.  Each
sense is a different way of asking "is this really *the* minimum
residue?" and each is answered by a separate Lean-formal proof.
The three readings bracket Raw from three directions and close
the uniqueness story.

  - **From below** (§4.1) — nothing weaker is enough.  Removing
    any clause collapses the framework to trivial, static, or
    void.
  - **Sideways** (§4.2) — nothing distinct is needed.  Any
    framework that does distinguishing factors through Raw.
  - **From above** (§4.3) — only one shape is self-consistent.
    Once arity and atomicity are imposed, the parameters
    `(NS, NT, d) = (3, 2, 5)` are forced.

A bundled statement asserting all three simultaneously lives at
`lean/E213/Meta/ThreeDirectionUniqueness.lean` (§4.4).

---

## §4.1 From below — clause removal collapses

The first uniqueness reading is the **minimum from below**:
weakening or removing any clause makes the framework collapse to
trivial, static, or void.  This is mechanically verified in
`lean/E213/Meta/AxiomMinimality.lean` and its capstone — a
four-case formalisation that walks through each clause (the two
atoms, the binary slash, the symmetry, the distinctness
precondition) and exhibits a collapse witness for its removal.

Two further structures formalise the same minimum-from-below
reading from different angles.  `Lens/SemanticAtom.lean` defines
the typeclass `HasDistinguishing` and its `universalMorphism`,
exhibiting Raw as the partial form of the initial object in the
distinguishing-framework category.  The same file's
`exists_non_lens_expressible` carries a boundary witness: not
every function `Raw → α` is Lens-expressible (depth parity is
the explicit counterexample, mechanised in
`Lens/Morphism/DepthParityNotFold.lean`).  This shows that the
Lens language is non-trivial — there are observables it does
not reach, which is what one wants of a framework that claims
not to be everything.

The truth-value type `Prop` itself can be put on the same
typeclass: with combine `propXor` or `Iff`, `Prop` is a
distinguishing-framework instance.  This brackets the framework
not just from outside (every other instance) but at the
meta-level (the language one is currently writing in).

All the above results are PURE under the falsifiability contract
(§8.2): `#print axioms` returns the empty list on every relevant
declaration.

---

## §4.2 Sideways — any framework factors through Raw

The second reading targets the question "could a framework
distinguish that *is* something different from Raw?"  The
answer, formalised in `lean/E213/Meta/UniversalLens/`, is no.
Any distinguishability framework factors through Raw via an
injective Lens view.

The crucial observation behind this reading is that
**"distinguishable from another" and "the difference being read"
are not two separate conditions**.  Without anything reading a
difference, no distinguishing has occurred; without difference,
nothing is read.  They are the same event.  The (Raw + Lens)
decomposition that the formal layer uses is a notational
convenience for readability, separating two sides of one event
so that proofs can address them independently.

### Raw as initial object

The technical content of "factors through" is the categorical
notion of an initial object.  The typeclass `HasDistinguishing`
in `lean/E213/Lens/SemanticAtom.lean` captures the abstract
shape of a distinguishing framework: two atoms (`a`, `b`), a
binary `combine`, and a `combine_sym` field stating that
`combine` is symmetric.  Read at this level, the 213 axiom is
**the unique Raw-level instance of `HasDistinguishing`** —
"unique" because the §4.1 minimality forbids any weakening, and
"Raw-level" because the axiom commits to no encoding beyond
what the abstraction itself requires.

Raw sits at the initial position in the category of
distinguishing frameworks.  Every other instance — `Bool` with
xor, `Prop` with `propXor` or `Iff`, function spaces with
pointwise combine, and so on — receives a unique morphism *from*
Raw via the catamorphism `Raw.fold`.  The companion theorem
`view_unique` at `lean/E213/Lens/Initiality.lean` certifies
the uniqueness side of this universal property explicitly: any
two morphisms `Raw → α` that agree on the basis and respect the
combine agree everywhere.  So when one writes "any
distinguishability framework factors through Raw," the technical
content is that **Raw is the initial object in the category of
`HasDistinguishing` instances with commutative-combine
homomorphisms**.

The witness families `Lens/Universal/Witnesses/{Core, Nat2,
Nat2Inj, Q213, Q213Inj, Nat3, Q213_3, TripleCapstone, Padding,
PaddingCapstone}` realise the factoring for the codomains that
Lean can handle directly.  An entity earns the description
"meaningful" exactly when it can serve as a `HasDistinguishing`
instance — and being a candidate is precisely receiving from
Raw via the universal morphism.

### What lies outside the picture

A useful contrast.  The objects committed to by ZFC's
arbitrariness axioms (Power, Choice, arbitrary `P(X)` subsets)
have no fold-structured representation
(`Lens/Morphism/NoDepthParity.lean`, `DepthParityNotFold.lean`).
They have no representation inside the 213 framework.  Whether
they "exist" outside it is an interpretive question under this
Lens — and the only answer 213 can offer is that the framework
provides no operand for the question.

The sideways reading does not close under the falsifiability
contract via Lean alone; it uses a Lens whose codomain reaches
beyond what Lean encodes.  This is not a weakness of the
reading.  Both §4.1 and §4.2 read the same residue, with
different Lens codomains.  The formal Lean coverage of the
meaning side is in `Lens/SemanticAtom.lean`.

---

## §4.3 From above — the forced shape

The third reading complements the first two with **only one
shape is self-consistent**.  Once arity and atomicity are
imposed (and these are themselves consequences of the axiom),
the shape parameters `(NS, NT, d) = (3, 2, 5)` are the unique
admissible solution.

The proofs live under `lean/E213/Theory/Atomicity/`:

  - `Five.lean` proves `atomic_iff_five`: a Raw shape is atomic
    if and only if its primitive carrier size is exactly 5.
  - `PairForcing.lean` proves that, once arity = 2 and
    atomicity are imposed, `(NS, NT, d) = (3, 2, 5)` is the
    **unique** admissible shape.
  - `ArityForcing.lean` and `ArityForcingGeneral.lean` close the
    gap by forcing arity = 2 itself from the §2 axiom (no unary,
    no ternary primitive).
  - `NonDecomposable.lean` and `Alive.lean` capture the
    sub-properties that the atomicity constraint pins down.
  - `PrimitiveSizes.lean` enumerates the sub-`d` candidate sizes
    that the constraint rules out.

These are **pure-ℕ proofs that do not import Raw**.  Their
independence is not "external view of Raw" — with no exterior
from which to set parameters (§5.1), the shape parameters
appear as the only self-consistent fixed point under the
constraints.  The from-above reading says: of all the shapes a
framework satisfying clauses 1–4 could take, exactly one
survives the atomicity + arity demands, and it is
`(NS, NT, d) = (3, 2, 5)`.

---

## §4.4 Bundled

The three readings are bundled into a single statement at
`lean/E213/Meta/ThreeDirectionUniqueness.lean`, which certifies
all three simultaneously: nothing weaker (`AxiomMinimality`),
nothing distinct (`UniversalLens` witnesses), only one shape
(`Atomicity` cluster).

The architectural placement of the atomicity proofs (under
`Theory/Atomicity/`) is canonicalised in
`lean/E213/ARCHITECTURE.md`.  Conceptually they belong to
Theory — they describe what Raw must look like — but their
proofs do not import Raw, which is the technical content of "the
shape is forced without any prior commitment to Raw's structure."
