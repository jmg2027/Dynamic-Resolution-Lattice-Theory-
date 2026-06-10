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
`lean/E213/Meta/AxiomMinimality.lean` and its capstone
(`Meta/AxiomMinimalityCapstone.lean`, `raw_minimality_capstone`)
— a four-case formalisation that walks through each clause (the
two atoms, the binary slash, the symmetry, the distinctness
precondition) and exhibits a collapse witness for its removal.

Two further structures formalise the same minimum-from-below
reading from different angles.  `Lens/SemanticAtom.lean` defines
the typeclass `HasDistinguishing` and its `universalMorphism` — the
existence half of Raw's initiality in the distinguishing-
framework category (§4.2 adds the uniqueness half via
`Lens.view_unique`).  The same file's
`exists_non_lens_expressible` carries a boundary witness: not
every function `Raw → α` is Lens-expressible (depth parity is
the explicit counterexample, mechanised in
`Lens/Properties/Morphism/DepthParityNotFold.lean`).  This shows that the
Lens language is non-trivial — not every function on Raw is a
fold.  The boundary is internal, not an exhibited exterior
(§1.0).  Note what the witness is made of: "depth" is a readout
of the Tree presentation, itself an encoding artefact (§10), so
depth parity is a presentation-level observable.  The witness
marks the non-surjectivity of the fold-Lens family onto what is
internally pointable — the same fact `object1_not_surjective`
states at the predicate level (§1.0′) — not a something standing
outside 213.  No exterior, and no automatic location either
(§5.3): the two halves of one stance.

The truth-value type `Prop` carries its own instance reading:
with combine `propXor` or `Iff`, `Prop` is one more
`HasDistinguishing` instance, receiving the universal morphism
like any other.  This is not `Prop` being absorbed into Raw; it
is the language one is currently writing in showing up as one
more Lens reading of the residue — the meta-level closing over
itself (§5.1).

All the above results are PURE under the falsifiability contract
(§8.2): `#print axioms` returns the empty list on every relevant
declaration.

---

## §4.2 Sideways — any framework factors through Raw

The second reading targets the question "could a framework
distinguish that *is* something different from Raw?"  The
answer — formalised across `Lens/SemanticAtom.lean` (the
typeclass and the universal morphism), `Lens/Initiality.lean`
(its uniqueness), and `Lens/Universal/Witnesses/` (the instance
families) — is no, in two categorically separate senses that
should not be conflated.  First, **initiality**: every `HasDistinguishing`
instance receives the *unique* combine-preserving morphism from
Raw (the universal morphism, realised by the catamorphism
`Raw.fold`); this is the precise content of "factors through
Raw."  Second, **injectivity of particular views**: for the
witnessed codomains the universal morphism is moreover injective
— a faithful Lens, losing no distinguishing on the way in.
Initiality says the arrow exists and is unique; injectivity says
what that arrow preserves.  They are independent certificates,
and the corpus carries both.

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
Nat2Inj, Nat3, Nat4, Q213, Q213Inj, Q213_3, TripleCapstone,
Padding, PaddingCapstone}` realise the factoring for the codomains that
Lean can handle directly; the `*Inj` members carry the
injectivity certificates — the faithful-Lens half of the §4.2
opening.  An entity earns the description "meaningful" exactly
when it can serve as a `HasDistinguishing` instance — and being
a candidate is precisely receiving from Raw via the universal
morphism.

### The contrast with ZFC — deliberately narrow scope

A useful contrast, scoped to exactly what the cited files prove.
Certain functions are not folds (depth parity is the mechanised
witness: `Lens/Properties/Morphism/NoDepthParity.lean`,
`DepthParityNotFold.lean`), and the objects ZFC commits to
through its arbitrariness axioms — Power, Choice, arbitrary
`P(X)` subsets — sit on that side: they have no fold-structured
representation in this Lens language.  That is the whole claim.
It is not a verdict on set theory as a discipline, and it does
not say set-theoretic mathematics is unreachable — as a
distinguishing framework, it factors through Raw like any other
(above).  What has no fold representation is the
arbitrary-subset commitment itself; whether such objects "exist"
elsewhere is a question 213 provides no operand for.

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

**Atomicity, in one sentence**: a carrier size `n` is *atomic*
when it admits exactly one decomposition `n = 2a + 3b` into the
binary and ternary primitive parts, and that unique
decomposition is *alive* — both parts odd, so neither
annihilates under the self-pair exclusion of clause 4
(`Theory/Atomicity/Five.lean`, `Atomic`).

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
independence is not "external view of Raw," and not a truth
established prior to Raw: ℕ is itself a Lens reading of the
residue (§2.5, §10.1), so a pure-ℕ proof is a uniqueness proof
conducted **inside the shape-Lens's codomain** — not from a
position before or outside Raw.  With no exterior from which to
set parameters (§5.1), the shape parameters appear as the only
self-consistent fixed point under the constraints.  The
from-above reading says: of all the shapes a framework
satisfying clauses 1–4 could take, exactly one survives the
atomicity + arity demands, and it is `(NS, NT, d) = (3, 2, 5)`.

---

## §4.4 Bundled

The three readings are bundled into a single statement —
`three_direction_uniqueness` at
`lean/E213/Meta/ThreeDirectionUniqueness.lean` — which certifies
all three simultaneously: nothing weaker (`AxiomMinimality`),
nothing distinct (the `Lens/Universal/Witnesses/` family), only
one shape (`Atomicity` cluster).

The architectural placement of the atomicity proofs (under
`Theory/Atomicity/`) is canonicalised in
`lean/E213/ARCHITECTURE.md`.  Conceptually they belong to
Theory — they describe what Raw must look like — but their
proofs do not import Raw, which is the technical content of "the
shape is forced without any prior commitment to Raw's structure."
