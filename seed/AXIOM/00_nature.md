# §1. Nature of the axiom

## §1.0 Position (formerly PHILOSOPHY.md)

The 213 axiom is **not** a declaration about "the foundation of the
world."  It is **the minimum residue that inevitably remains the moment
one tries to point at something**.

- The moment one writes "a and b," "and" is also something.
- The moment one writes "a, b," "," is also something.
- Are a and "and" distinguished? What distinguishes them? Yet
  another something.

Notation, the moment it begins, endlessly produces new somethings.
Recursion is unavoidable.  The axiom is the *minimum expression* of
that recursion — not eliminating it, but recording it in a form where
recursion operates only minimally.

Since the axiom is a **residue**, not a declaration, it is not subject
to choice.  It cannot be made "more minimal," nor can "more" be added.
Minimality is already guaranteed; adding anything beyond it fails the
audit.

### Primitive distinction, not "relation"

- "Relation" presupposes two existing somethings + silently imports
  set-theoretic properties.
- "Primitive distinction" — distinction operates *first*, requires
  only "not equal."
- "Primitive" = pledge of no further reducibility.

### Linguistic inevitability

Even "primitive distinction" is not perfect.  "Difference" presupposes
"sameness"; "and" reads as a conjunction; "," is a separator.
There is no perfect expression.  Current words are *minimum-commitment
expressions*, used with acknowledgment of residual import.
**Minimization is possible; elimination is not.**

### Status of "something"

From the moment one says "something," is it already a Lens?  Possibly.
Is 213 Platonic ideals?  Probably not.  These questions are *open* and
do not affect the usefulness of 213.  What matters is whether
derivation succeeds, not ontology.

---

## §1.1 Formal core: strict minimum of the Raw axiom

The 4-case formalization in `lean/E213/Meta/AxiomMinimality.lean`
(+ `AxiomMinimalityCapstone.lean`) — removing or weakening any clause
(a, b, slash, distinctness) of Raw causes the framework to collapse to
trivial / static / void.  This is the framework-internal proof that
the Raw axiom is the strict minimum of "two distinguishable bases +
binary combine + distinctness."

Results from `lean/E213/Lens/SemanticAtom.lean`:
- `HasDistinguishing` typeclass + `universalMorphism` — Raw as the
  partial form of the initial object in the distinguishing-framework
  category (generalization of RawInitiality).
- `IsLensExpressible` definition + `exists_non_lens_expressible` —
  not every Raw → α function is Lens-expressible (non-trivial
  boundary).  Witness: depth parity
  (`Lens/Morphism/DepthParityNotFold.lean`).
- `Prop` instance (Xor + Iff alternatives) — the truth-value type of
  the metalanguage can also be an instance of the distinguishing
  framework.

The above results are the self-justified core of the framework.  No
external metatheory — `#print axioms` reports [propext, Quot.sound] or
no axioms for all results.

§1.1 and the **Universal Lens metatheory** in
`lean/E213/Meta/UniversalLens/` are complementary statements — the
former proves Raw cannot be weaker (clause removal collapses), the
latter proves any distinguishable codomain factors through Raw via an
injective Lens view (`Meta/UniversalLens/{Core, Nat2Inj, Q213Inj,
TripleCapstone}`).  Together they bracket Raw both from below ("can't
remove") and from above ("everything else maps in").

---

## §1.2 Conceptual extension (philosophical)

**Note**: a *philosophical extension* on top of the formal core.  No
direct formal Lean verification — interpretive scope.

The formal core of §1.1 motivates the following conceptual extension:

- **Two conditions for meaning to arise**: for any entity to have
  meaning, (1) it must be distinguishable from other entities, and
  (2) that difference must be interpretable.  The (Raw + Lens) of 213
  is the minimum candidate satisfying these two conditions.
- **Ontological reading**: accepting "something exists" =
  "is distinguishable from something else," every meaningful entity
  becomes a candidate instance of 213.
- **Comparison with ZFC**: the objects committed to by ZFC's
  arbitrariness axioms (Power, Choice, arbitrary P(X) subsets, etc.)
  have no fold-structured representation
  (`Lens/Morphism/NoDepthParity.lean`,
  `Lens/Morphism/DepthParityNotFold.lean`).  I.e., no
  representation inside the 213 framework — their semantic status is
  an interpretive question.

This conceptual extension is analyzed in
`research-notes/75_semantic_atom.md` and
`research-notes/76_ultimate_ouroboros.md`; current Lean coverage in
`Lens/SemanticAtom.lean`.  It can be connected to the
physics intuition chain in `seed/ORIGIN.md` — formal Lean results
serve as evidence for that interpretation.

**Boundary**: §1.1 (formal core) is verifiable within the
falsifiability contract.  §1.2 (philosophical extension) is a
semantic explanation of the framework — not elevated to a formal
claim.

---

## §1.3 Forced shape uniqueness — d=5 is a theorem

A *third* pillar of axiom uniqueness, complementing §1.1 (minimality
from below) and §1.2 (universality / philosophical extension), is
formalized in `lean/E213/Theory/Atomicity/`:

- `Five.lean` — `atomic_iff_five`: a Raw shape is atomic iff its
  primitive carrier size is exactly 5.
- `PairForcing.lean` — once arity = 2 and atomicity are imposed,
  `(NS, NT, d) = (3, 2, 5)` is the *unique* admissible shape.
- `NonDecomposable.lean`, `Alive.lean` — sub-properties forced by
  the same atomicity constraint.
- `ArityForcing.lean`, `ArityForcingGeneral.lean` — arity = 2 is
  itself forced by the §3 axiom (no unary, no ternary primitive).
- `PrimitiveSizes.lean` — enumeration of sub-d primitive sizes
  ruled out as non-atomic.

These are **pure-ℕ proofs that do NOT import Raw**.  They are an
external uniqueness obligation: "if Raw exists at all, its shape
parameters are forced."  Together with §1.1 ("Raw is minimum from
below"), §1.2 ("any framework factors through Raw"), this closes
the uniqueness statement to all three directions:

- below — nothing weaker is enough          (Meta/AxiomMinimality)
- sideways — nothing distinct is needed     (Meta/UniversalLens)
- above — Raw's own shape is forced         (Theory/Atomicity)

The architectural placement of these proofs (Theory/Atomicity/)
is canonicalized in `lean/E213/ARCHITECTURE.md`.  Historical note:
an earlier `OS/` directory was first retired (atomicity proofs
absorbed into Theory/Atomicity/) and later partially re-instated
as the orchestration layer.  The atomicity material did not move
back.
