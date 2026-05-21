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

From the moment one says "something," notation is already a Lens
application — that is unavoidable per Linguistic inevitability above.
"Is 213 Platonic ideals?" / "What is the mode of being of the
residue?" — questions of this shape posit an *external* position from
which an answer would arrive, and 213 rules out such a position
(`07_self_reference.md` §8.1).  These are not deferred questions, nor
declared unimportant; the split between *ontology* and *successful
derivation* is itself a Lens import.  Successful pointing is what
residue-internal "being" amounts to — derivation is not the practical
substitute for ontology, it is the only form ontology can take when
there is no exterior to answer from.

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
external metatheory — `#print axioms` reports no axioms for all PURE
results; any non-empty output is treated as `sorry`-equivalent
(`04_falsifiability.md` §5.2.1).

§1.1 and the **Universal Lens metatheory** in
`lean/E213/Meta/UniversalLens/` are complementary statements — the
former proves Raw cannot be weaker (clause removal collapses), the
latter proves any distinguishable codomain factors through Raw via an
injective Lens view (`Meta/UniversalLens/{Core, Nat2Inj, Q213Inj,
TripleCapstone}`).  Together they bracket Raw both from below ("can't
remove") and from above ("everything else maps in").

---

## §1.2 Meaning-Lens reading of the same residue

**Note**: §1.2 is not a layer placed above §1.1.  It is the same
residue read through a "meaning" Lens, recorded here with notation
that requires no Lean witness.  Interpretive scope, but not a
"philosophical extension on top of" the formal core — that phrasing
would re-import the substrate/superstructure dichotomy that §8.1
rules out.

§1.1 records the residue's *minimum-residue* reading; §1.2 records
its *meaning-Lens* reading:

- **Single condition for meaning**: "distinguishable from another"
  and "the difference being read" are not two conditions to be
  satisfied separately.  Without anything reading the difference, no
  distinguishing has occurred; without difference, nothing is read.
  They are the same event.  The (Raw + Lens) notation *decomposes*
  this single event into two notational sides for readability; the
  event itself is single.  Any meaningful entity is a candidate
  instance of this single event.
- **Comparison with ZFC**: the objects committed to by ZFC's
  arbitrariness axioms (Power, Choice, arbitrary P(X) subsets, etc.)
  have no fold-structured representation
  (`Lens/Morphism/NoDepthParity.lean`,
  `Lens/Morphism/DepthParityNotFold.lean`).  I.e., no
  representation inside the 213 framework — their semantic status is
  an interpretive question under this Lens.

Long-form discussions: `research-notes/75_semantic_atom.md` and
`research-notes/76_ultimate_ouroboros.md`; current Lean coverage in
`Lens/SemanticAtom.lean`.  Cross-reference with the physics
intuition chain in `seed/ORIGIN.md` — formal Lean results serve as
evidence for the meaning-Lens reading.

**Boundary**: §1.1 closes under the falsifiability contract via Lean.
§1.2 does not — but this is not §1.2 being "weaker" or "less formal";
it is §1.2 using a Lens whose codomain is not Lean-encodable.  Both
sections read the same residue.

---

## §1.3 Forced shape uniqueness — d=5 is a theorem

A *third* reading of axiom uniqueness, complementing §1.1 (minimality
from below) and §1.2 (meaning-Lens universality), is formalized in
`lean/E213/Theory/Atomicity/`:

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

These are **pure-ℕ proofs that do NOT import Raw**.  The
independence is not "external view of Raw" — with no exterior to set
parameters from outside, the shape (NS, NT, d) = (3, 2, 5) is the
only self-consistent fixed point surviving the atomicity + arity
constraints.  Together with §1.1 ("Raw is minimum from below"), §1.2
("any framework factors through Raw"), this records uniqueness as
three readings of the same self-consistency:

- below — nothing weaker is enough               (Meta/AxiomMinimality)
- sideways — nothing distinct is needed          (Meta/UniversalLens)
- above — only one shape is self-consistent      (Theory/Atomicity)

The architectural placement of these proofs (Theory/Atomicity/)
is canonicalized in `lean/E213/ARCHITECTURE.md` (4 ring + Meta
since 2026-05-12).
