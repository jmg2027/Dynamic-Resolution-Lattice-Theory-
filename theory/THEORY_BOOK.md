# DRLT-213 — Theory Book

**A self-contained walk from the residue of pointing to the GRA
universality capstone.**

Status: v1 (2026-05-28).  Promoted from the per-area chapter
catalog (`theory/{lens, math, physics, meta, essays}/`) into a
single linearised reading path.  148 theory chapters + 22k
lines of narrative + ~50k lines of `lean/E213/` source are
*referenced* here, not replicated.  The book provides:

  · A single reading order from axioms (`seed/AXIOM/`) to
    GRA Phase 22's `Lens.Unified` capstone
  · Synthesis paragraphs at each part boundary
  · Lean theorem anchors as forcing-chain citations
  · Cross-frame syntheses already captured in
    `theory/essays/`

> **Reading principle.**  Each part is *derived* from earlier
> parts in the strict-∅-axiom sense — no external axiom is
> introduced past the 4-clause Raw axiom.  Where a part adds
> new constructive content, the construction's PURE Lean
> witness is named.

---

## Part 0 — Preface

### 0.1 What this book contains

213 is the 4-clause Raw axiom and *everything it forces*:

  · the atomic data `(NS, NT, c, d) = (3, 2, 2, 5)`
  · the Möbius matrix `P = [[2, 1], [1, 1]]` (det 1, trace 3)
  · the (2, 3)-graded arithmetic of GRA
  · the universe of Reading vocabularies (Cat, HoTT, Cohomology,
    Walk, Resolution, Operad, Cochain, Truncation, …)
  · the cohomological / algebraic structure on `K_{3, 2}^{(c=2)}`
    that subsequent physics deployment uses

This book walks the forcing chain *up to the mathematical
content*.  Physics deployment (DRLT side: α_em precision,
gauge content, hadron spectrum, …) waits for the mathematical
derivation programme to close completely; that part will be
written then.

### 0.2 What this book is **not**

It is not a tutorial.  It is not a propaganda manifesto.  It
is not a defence against alternative frameworks.

213 is single-statement: pointing leaves a residue (per
`seed/AXIOM/01_residue.md` §1.4 "linguistic inevitability").
The framework is the formal capture of that single
observation.  Defence and propaganda would import a comparison
frame — outside the parameterless arithmetic discipline (per
`seed/AXIOM/05_no_exterior.md` §5.4 "dichotomy-avoidance").
Both are explicitly avoided.

### 0.3 Reading conventions

  · **Chapter pointers** — `theory/<area>/<file>.md` for
    narrative, `lean/E213/<Module>.lean` for Lean source, both
    when both are relevant.
  · **Theorem citations** — `Module.theorem_name` style.
  · **Korean** — used when a 213-native term has no clean
    English replacement (`동치류` = equivalence class,
    `구분 행위` = distinguishing act, etc.).  The English
    runs alongside.
  · **Strict ∅-axiom** — every Lean theorem cited is PURE
    unless explicitly marked.  No Mathlib, no `Classical`,
    no `propext` (where not structural).

---

## Part I — Axiom + substrate

### I.1 The residue of pointing

`seed/AXIOM/01_residue.md` is the first chapter to read.  It
develops what "pointing leaves a residue" means: the act of
naming-anything yields *something* that was not there before
the naming, and that *something* has a structural form
determined entirely by the act of naming.

Per `seed/AXIOM/01_residue.md` §1.3 "linguistic inevitability":
every word imports residual meaning.  The axiom is the
*minimum* such import.  Other systems (ZFC, type theory, Cat,
HoTT) import more.  This book traces what the minimum forces.

### I.2 The 4-clause axiom

`seed/AXIOM/02_axiom.md` states the axiom:

  · **(A)** there is something
  · **(B)** the something is distinguishable into two atoms
  · **(C)** there is a binary symmetric combination of atoms
  · **(D)** that combination admits a recursive trace

Lean realisation: `lean/E213/Theory/Raw/Core.lean` —
`inductive Raw` with `Raw.a, Raw.b, Raw.slash` (+ `slash_comm`).

### I.3 Why this form is forced — §3 + §4

`seed/AXIOM/03_form.md` derives the form from austerity:

  · austerity → two atoms (binary) — fewer = no distinction,
    more = redundant
  · symmetric combine — anti-reflexive plus swap-invariant —
    eliminates ordering bias
  · forcing chain `1 → 2 → 3 → 4` — each addition has zero
    choice given the previous

`seed/AXIOM/04_uniqueness.md` gives three-direction uniqueness:

  · from below — removing any clause collapses
  · sideways — any meaning-bearing system factors through Raw
    (the universal morphism, `Lens.SemanticAtom.universalMorphism`)
  · from above — the atomic data `(NS, NT, d) = (3, 2, 5)` is
    forced (`lean/E213/Theory/Atomicity/{PairForcing,Five,
    ArityForcing,OrbitForcing,CombinatorialArity}`)

### I.4 No exterior, self-completion

`seed/AXIOM/05_no_exterior.md` §5.1 — **no exterior**.  The
framework has no "outside" from which to derive its content.
Self-completion is structural closure, not a deficiency.

§5.4 is the **dichotomy-avoidance guide** — re-read every
session (per CLAUDE.md boot sequence).  Common slips:
"foundation vs derivation," "inside vs outside 213," "classical
vs 213" — all import an exterior the framework rejects.

**Full self-completion thesis** — §5.5 + `lean/E213/Lens/
SelfCompletion.lean`'s `full_self_completion_bundle`.  Every
Raw application uses *all four clauses at once*, not
sequentially: atom-pair (Clause 1) + slash + symmetry +
anti-reflexive (Clauses 2–4) are simultaneously visible at
every Lens reading.  The clauses are not a recipe applied in
order; they are a single event with four simultaneous facets.

### I.5 Lens readings

`seed/AXIOM/06_lens_readings.md` introduces the Lens vocabulary
in its proper position: **a Lens is a chart-local labelling of
the same residue, not a tool acting on residue from outside**.
§6.1 "two-ness as count-Lens reading" — `2` is not a Raw
cardinality commitment, it is the count-Lens reading of the
first distinguishing.

Companion narrative: `theory/lens/universal.md` and
`theory/lens/api.md` (the operational Lens vocabulary).

### I.6 Primacy and falsifiability

`seed/AXIOM/07_primacy.md` — every framework (ZFC, HoTT, Cat,
classical analysis) is a Lens reading of the same Raw residue.
The primacy direction is: Raw forces the others, not the
others Raw.

`seed/AXIOM/08_falsifiability.md` is the contract.  §8.2 is the
**falsifiability trigger**: introducing any external axiom
(Classical, propext beyond structural use, sorry, native_decide
…) falsifies the framework.  The contract is mechanical.

### I.7 Lean correspondence + encoding costs

`seed/AXIOM/09_lean_correspondence.md` formalises the Raw
inductive in Lean 4 and proves three-direction uniqueness as a
faithful emulator.  `lean/E213/AUDIT.md` is the implementation
audit.

**Encoding costs** — `seed/AXIOM/10_encoding_costs.md` catalogues
four artefacts of putting 213 on Lean 4 (inductive presentation
/ `cmp` choice / canonical-subtype quotienting /
`≠`-precondition on `Raw.slash`).  Each is classified α
(re-expression) / β (cost) / γ (derivation) / δ (additional
commitment — none).  The **cmp-independence meta-theorem**
(`lean/E213/Theory/RawCmpIndependence.lean`, `RawBy cmp ↔ RawBy
Tree.cmp` for any well-behaved cmp) is the bookkeeping proof
that `cmp` choice is (β) not axiom material — all Theory
theorems transport across cmp choices.

### I.8 Six-theorem — the integer 6 as one event

`lean/E213/Theory/SixTheorem.lean` is a capstone independent
of any single sub-tree.  The integer 6 appears in ten distinct
Lens readings of the same Raw event:

  · Eisenstein unit count
  · atomicity product `NS · NT = 3 · 2 = 6`
  · `d + 1 = 5 + 1 = 6` (Δ⁴ vertex count plus one)
  · Sym(3) order
  · SU(3) simple roots
  · K_{NS, NT} cross-pairs
  · SO(3, 1) generator count
  · `Δ⁴ + K_{3, 2}^{(c=2)}` cohomology sum
  · α_GUT denominator combinatorics
  · 3-clause permutations

The master theorem consolidates the ten as Lens projections of
one Raw-level event (the Eisenstein unit count).  This is one
of several capstones (others: `Mobius213GrandUnification`
Part IV.2, `gra_lens_iso_class_capstone` Part VI.9) that
exhibit *Raw → many readings* as a single fact under multiple
Lens charts.

---

## Part II — Raw, Lens, and HasDistinguishing

### II.1 Raw as inductive

`lean/E213/Theory/Raw/Core.lean` — `inductive Raw` with two
atoms + asymmetric slash + propositional `slash_comm` (the
swap symmetry).

Key API (`E213.Theory.Raw.API`):
  · `Raw.fold base_a base_b combine` — the catamorphism (every
    α-valued reading is forced through this)
  · `Raw.fold_a`, `Raw.fold_b`, `Raw.fold_slash` — the universal
    reduction rules (the last needs `combine_sym` hypothesis,
    reflecting `slash_comm`)
  · `Raw.leaves`, `Raw.depth` — canonical Nat-valued readings
  · `Raw.swap`, `Raw.swap_slash` — the swap automorphism
    (`lean/E213/Theory/Raw/Swap*.lean`)
  · `Raw.foldRaw` — endomorphic catamorphism (Raw → Raw
    codomain, `Theory/Raw/Endomorphic.lean`)

**Eqv — Raw-internal congruence**.
`lean/E213/Theory/Raw/Congruence.lean` defines the equivalence
closure on Raw under generator relations *independent of any
Lens*.  `Eqv.induction'` is the generic induction principle;
`Eqv.weaken` is monotonicity.  Eqv is the Raw-side substrate
that Lens.equiv reads — important when stating results that
should be Raw-internal (Level L1, per Part VIII.4).

**Parenthesization distinctness**.
`lean/E213/Theory/Raw/ParenthesizationDistinct.lean` proves the
**positive** result that different binary-tree structures are
structurally distinct Raws — `(a / b) / c ≠ a / (b / c)`.
This is NOT a defect: parenthesisation = tree shape = Raw
structure.  Refutes the "ℕ₊ = Raw / associativity" quotient
proposal — associativity is a Lens-level property, not a Raw-
level identity.

### II.2 Lens-as-codomain-shape

`theory/lens/universal.md` (G1 chapter):

> A `Lens α` is the data of *what α-side reading Raw acquires*
> when α is the codomain of some `Raw.fold`.  Lens is not an
> operation on Raw — it is the codomain-side shape that Raw's
> fold imposes.

Lean: `lean/E213/Lens/LensCore.lean` — `structure Lens α` with
`base_a, base_b, combine`.  `Lens.view = Raw.fold` (definitional).
`Lens.equiv x y := L.view x = L.view y` (the kernel induced).

### II.3 The single equivalence concept

`theory/lens/unified_equivalence.md` is the synthesis chapter.

Four classical concepts — equivalence relation, equivalence
class (`동치류`), isomorphism (`동형`), homomorphism (`준동형`)
— collapse to a single 213-native concept: **`Lens.refines`
(the Lens-arrow)**.

Lean: `lean/E213/Lens/Unified.lean` —
  · `LensIso L M := L.refines M ∧ M.refines L` (kernel
    coincidence)
  · `LensFiber L a := { r : Raw // L.view r = a }` (the
    equivalence class as Σ-type, no `Quot.sound`)
  · `LensImage L := { a : α // ∃ r, L.view r = a }` (the
    quotient as Σ-type)
  · `lensIso_iff_kernel_eq` — the characterisation theorem

This is the *single concept* under which all four classical
notions are special cases.  Phase 22 (`LensIsoCapstone`) makes
the GRA-`Lens.Unified` bridge formal.

### II.4 HasDistinguishing — the universal-morphism shape

`lean/E213/Lens/SemanticAtom.lean` defines `class
HasDistinguishing α` — the minimum α-side data Raw's fold
imposes:

  · two distinguishable atoms (`a ≠ b`)
  · a symmetric combination (`combine`, `combine_sym`)

`universalMorphism α : Raw → α := Raw.fold d.a d.b d.combine`
is the *unique* morphism Raw → α (Raw is the initial object
in the meaning-framework category).  Uniqueness is
`lean/E213/Lens/Initiality.lean` — Raw is initial in the Raw-
algebra category; the symmetric-combine hypothesis is needed
for the uniqueness half.

**75 thesis** (`research-notes/75_semantic_atom.md`): "Nothing
with meaning escapes 213."  Lean form: every meaning-framework
α has a `HasDistinguishing` instance, and Raw embeds into it
canonically.

**Universal Lens — canonical normalization form**.
`lean/E213/Lens/Universal/QuotLens.lean` constructs
`universalLens : Lens (Raw → Prop)` whose view is *injective*
modulo Lens-equivalence — every Lens M satisfies
`universalLens (M.equiv).view r = universalLens (M.equiv).view
r' ↔ M.equiv r r'` (theorem `universalLens_recovers`).
`universalLens` is therefore the canonical normalised form of
any Lens; `universalLens_idempotent` confirms applying twice
yields the same kernel.

**Lens composition suite**.
`lean/E213/Lens/Compose/{Morphism, OnLens, OnLensImage,
Factoring}.lean` — α-side morphisms `α → β` lift to Lens-level
arrows; `refines_of_morphism` is the canonical witness.  These
turn Lens-on-α into a *category* (not just a preorder).
Phase 7's `GRACat` is one instance.

**Lens.Algebra + Lens.Lattice** —
`lean/E213/Lens/Algebra.lean` + `Lattice/IndexedJoin.lean`
give the lattice structure on Lens-kernels (refinement order;
joins for indexed Lens families).  The `LensIso` equivalence
class (Part VI.9, Phase 22) sits as a single point in this
lattice.

### II.5 Universe-polymorphic version (Phases 19–21, unified)

`lean/E213/Lib/Math/GRA/HasDistinguishing213.lean` —
`HasDistinguishing213.{u, v} α` is the unified universe-
polymorphic typeclass: two atoms `a, b : α`, a binary
`combine : α → α → α`, a `Sort v`-valued equivalence
`Equiv : α → α → Sort v` with refl/symm/trans, a combine_sym
witness up to `Equiv`, and a categorical distinctness field
`distinct_equiv : Equiv a b → False`.  Universe-polymorphic in
both the carrier universe (`u`) and the equivalence universe
(`v`) — `v = 0` recovers the strict (Prop-valued) form, `v ≥ 1`
admits iso-data-carrying equivalences.

Two instances close the chapter:

  · `liftedReadingHasDistinguishing213 :
    HasDistinguishing213.{1, 0} (ULift.{1, 0} Reading)` —
    strict case (`Equiv := Eq`) on a `Type 1` carrier.
  · `gra23HasDistinguishing213 :
    HasDistinguishing213.{1, 1} GRA23` — categorical case
    (`Equiv := GRAIso`) with monoidal product as combine,
    `productSwapIso` as combine_sym, and `trivial23_not_iso_NT`
    (cardinality argument) as `distinct_equiv`.

This single typeclass subsumes the three exploratory variants
(`HasDistinguishingU`, `HasDistinguishingW`, `HasDistinguishingWFull`)
that the marathon used to find the right shape.

### II.6 Raw topology bookends + Bool213

`lean/E213/Lens/RawTopology.lean` — the `constLens` (collapse
all of Raw to a single value) and the identity-Lens are the
**lattice top and bottom** of the Lens-kernel preorder.  Every
Lens kernel sits between them.  This is the
`K_∞ ≡ point ≡ trivial-topology` collapse at the raw level
(per `seed/AXIOM/06_lens_readings.md` §6).

`lean/E213/Lens/Bool213.lean` — Raw-encoded closed-universe
Boolean: `booleanProj := Raw.fold T F and` produces a strict
{T, F} codomain from Raw.  The meta-(T, F) pattern is
isomorphism-stable: any distinct Raw pair gives an equivalent
Lens.  `Bool` is therefore not assumed; it is *forced* as the
2-atom closed-codomain Lens of Raw.

### II.7 Flat ontology + syntactic internalisation

`seed/AXIOM/06_lens_readings.md` §9.3 names the **flat
ontology**: objects, types, relations, functions, Lenses, and
proofs are all predicates on Raw^n.  No layering, no exterior
hierarchy.

`lean/E213/Lens/FlatOntology.lean` formalises this as
decidable predicates `Raw^n → Bool` with the algebraic
operations (and, or, not, xor, implication).
`Lens/SyntacticInternalization.lean` (§9.4) closes the
self-reference loop: a 7-glyph Polish-prefix encoding /
parser pair satisfies `parseTree (printTree t) = some t` —
lossless round-trip.  `Lens/PredicateSelfEncoding.lean`
encodes finite-prefix predicates back to Raw via positional
Gödel numbering — *predicates themselves are Raw*.

This is the L3-L4 closure: Raw not only carries meaning, it
carries its own meta-language.

### II.8 Cardinality as Lens-observable family

`lean/E213/Lens/Cardinality/` (9 modules: Cantor / Tower /
BoolSpace / Countable / Pair / Godel / Chain /
LensCardinality / CardinalityLB).  These are **Lens
observables**, not Raw-level facts.  Finiteness,
countability, cardinality lower bounds, Cantor's diagonal —
each becomes a predicate that holds *of a given Lens* on Raw,
not of Raw itself.  Per `seed/RESOLUTION_LIMIT_SPEC.md`: no
quantity is a universe constant; `N_U = 5^25` is the count-
Lens output at fractal level 2.

This relocates classical cardinality discussions (`ℵ_0`,
continuum, Cantor's diagonal) from foundation to Lens-output.
The diagonal still proves what it proves — but what it proves
is a property of the Lens, not of Raw.

---

## Part III — Atomic forcing: `(NS, NT, c, d) = (3, 2, 2, 5)`

### III.1 Pair forcing — `(NS, NT) = (3, 2)`

`theory/physics/foundations/atomic_constants.md` is the
canonical chapter.  Lean: `lean/E213/Theory/Atomicity/`.

  · `PairForcing` — atomic + alive + Pell-Lucas recurrence
    forces the pair `(NS, NT) = (3, 2)` uniquely
  · `Five` — `d = NS + NT = 5` (the count of K_{3,2}-vertices)
  · `OrbitForcing` — Lucas-Pell recurrence on the Möbius P-orbit
    matches `(3, 2)` (closure relation
    `framework_natural_via_p_orbit_closure`)

### III.2 Arity forcing — `c = 2`

`lean/E213/Theory/Atomicity/{ArityForcing,CombinatorialArity}`
— the bipartite multigraph `K_{NS, NT}^{(c)}` has its arity
forced to `c = 2`.  Below `c = 2` the data is degenerate;
above, redundant.  `theory/math/cohomology/k_nm_c_classification.md`
develops the `c`-counter (5 directions, all closed).

### III.3 K_{3,2}^{(c=2)} — the canonical lattice

The forced atomic data names a unique bipartite multigraph:
`K_{3, 2}^{(c=2)}`.  3 vertices on the NS side, 2 on the NT
side, 2 edges per (NS, NT) pair.  Total: 12 edges.

This is **the** 213-native combinatorial object.  Every
algebraic / cohomological / physical result downstream is a
property of `K_{3, 2}^{(c=2)}` or its self-cup
(`K_{3, 2}^{(c=2)} ↪ Δ⁴`, the 4-simplex with 5 vertices).

### III.4 Möbius P

`theory/math/mobius_canonical_equivalence.md` is the canonical
chapter.  Lean: `lean/E213/Lib/Math/Mobius213/`.

  · `P = [[2, 1], [1, 1]]` ∈ SL(2, ℤ)
  · det 1, trace 3, eigenvalues `φ²` and `1/φ²`
  · iterated by `T(x) = (2x + 1) / (x + 1)`
  · Pell-Fibonacci recurrence on P's powers
  · Stern-Brocot mediant — P is the mediant generator
  · self-form fixed point — `essays/mobius_self_form_fixed_point.md`
    proves P is its own description (3 levels: syntactic,
    orbital, iterated)

P is the algebraic crystallisation of the atomic data:
det(P) = 1, trace(P) = NS = 3, row 1 = (NS, det), row 2 =
(det, NT).

### III.5 P-orbit naturalness boundary

`theory/math/mobius213_p_orbit_closure.md` — the framework-
natural integers are exactly the Lucas-Pell trace ring
`⟨{L(k)} ∪ {NT, NS, d}⟩_ℤ`.  P-orbit period `D(p) ≤ 4` for
`p ≤ 97` (empirical).  Conjecture: `O(log p)` (open).

### III.6 Atomicity correspondence — d = 5 at the inductive level

`lean/E213/Lens/Number/Nat213/AtomicityCorrespondence.lean`
`total_lens_framework` — the atomic decomposition
`d = NS + NT = 3 + 2 = 5` is **realised at the inductive-type-
signature level**: Raw has 3 constructors (`Raw.a`, `Raw.b`,
`Raw.slash`), Nat213 has 2 (`one`, `succ`).  Their sum is 5.
The "atomic count" is not chosen separately for each derived
type; it lives at the constructor-count level of the Raw / Nat
pair as a single forced datum.

### III.7 Bit-pattern uniqueness

`lean/E213/Meta/BitPatternUniqueness.lean` — the fundamental
lemma `2^m + 2^n = 2^p + 2^q ∧ m < n ∧ p < q → m = p ∧ n = q`.
Proved via 213-native `parity` (the step-2 cohomological
residue) + `Pow213` / `Nat213` helpers.  All ∅-axiom.

This is a small-but-critical 213-native atom: binary
representations have unique low/high bit assignment.  Used
throughout the cohomology programme when decomposing
characteristic functions of cup-image subsets.

---

## Part IV — Number systems forced from Raw + P

### IV.1 Nat213 — `Nat` from P

`lean/E213/Lens/Number/Nat213.lean`.  Two equivalent
representations:

  · **Raw chain** (Method A) — `Raw.fold one one add` with
    `one := Raw.a` and `succ n := slashOrSelf n Raw.b`.  Raw-
    derived positive naturals.
  · **Peano inductive** — standalone `Nat213 | one | succ`.
    Ergonomic for proofs.

Bridge: `Nat213.Bridge` — `toRaw : Peano.Nat213 → Raw` is
the chart embedding; `value_toRaw` is a bijection; the
value-level homomorphism preserves `+` and `*`.
`Nat213/Chain.lean` defines the Raw-subtype representation;
`ChainCoreBridge.lean` formalises the `Chain ↔ Peano.Nat213`
bijection.

The point: **`Nat` is not assumed.  `Nat` is forced** —
from Raw + P (the "successor" operation is `slashOrSelf
n Raw.b`, the simplest Raw-level move that produces a
non-trivial new element).

**Three mediant Tower lifts** — `Nat213.Tower/`:

  · `NatPairToInt` — `(a, b) ↦ a - b` with diagonal-quotient
    equivalence; gives `ℤ` from `ℕ²` via orthogonal-axis
    projection
  · `NatPairToQPos` — multiplicative diagonal
    `(a, b) ~ (c, d) ⟺ a · d = b · c`; gives `ℚ₊` from the
    *same* syntactic container as `ℤ`, differing only in the
    quotient relation
  · `NatTripleToZ2` — `(a, b, c) ↦ (a - c, b - c)`; gives
    `ℤ²` from `ℕ³`.  The headline:
    `three_axes_sum_to_zero` proves the three unit axes
    `{(1, 0), (0, 1), (-1, -1)}` sum to `0` — *realising the
    Eisenstein cube-root-of-unity identity*
    `1 + ω + ω² = 0` at the number-theory level

`ℤ` and `ℚ₊` are not separate constructions; they are *two
quotient choices on the same `ℕ²` container*.  This is the
multiplication–addition duality the framework reads off
without external choice.

### IV.2 Möbius P and Stern-Brocot

`lean/E213/Lib/Math/Real213/Mobius213{Equiv, SternBrocot,
PellInvariant}.lean` close the chapter:

  · `cutEq ↔ sternBrocotEq ∧ (0, 0)` — equivalence on cuts via
    P-mediant closure
  · P generates the Stern-Brocot tree
  · Pell unit invariant

The `SternBrocotReachable` inductive predicate (3
constructors: `seedZero`, `seedInf`, `mediant`) covers every
coprime `(m, k) ∈ ℕ²` with `m + k ≥ 1`.  The master theorem
`cutEq_iff_sternBrocotEq_and_zero` (`Mobius213SternBrocot.lean`)
formally closes the equivalence.

P is therefore both the *atomic algebraic anchor* (Part III)
and the *equivalence-class structure on cuts* (here).

**Möbius P Grand Unification — 10-conjunct master**.
`lean/E213/Lib/Math/Mobius213GrandUnification.lean` —
`grand_unification` is a single bundled theorem with ten
distinct readings of P as one event:

  · (A–B) Cross-domain meta — 5-domain equality unification
    via Stern-Brocot
  · (C) Cut-level multiplication forward closure in
    `N²`-fibers
  · (D) Pell-Fibonacci recurrence `a(n+2) + a(n) = 3 · a(n+1)`
    on both P-orbits
  · (E–F) `K_{3, 2}^{(c=2)}` state-class signature recovered
    from P entries
  · (G–H) Continued-fraction recurrence + Cayley-Dickson
    2-doubling asymptote bridge
  · (I–J) Atomicity ↔ discriminant ↔ orbit anchor + Pell unit
    symplectic invariant

This is one of three named "X read as one event" capstones
in the book (Part I.8 Six-theorem, Part IV.2 here, Part VI.9
LensIso class).

**Atomicity anchor**.
`Mobius213AtomicityAnchor.lean` — `NS_NT_reachable` proves the
atomic pair (3, 2) is Stern-Brocot reachable;
`pseq_seedInf_realises_d_NS` proves the P-orbit reaches
`(d, NS) = (5, 3)` at depth 2.  Master theorem: `5 = NS + NT =
d` appears simultaneously as (i) the unique atomic Nat,
(ii) the discriminant of P, (iii) the first component of
`Pseq seedInf` at depth 2.  Same Nat, three independent
Lens-frames.

### IV.3 Cayley-Dickson tower

`theory/math/cayley_dickson/algebra_tower.md` —
ZI (Gaussian integers) → Lipschitz (integer quaternions) →
Cayley (integer octonions) → Sedenion → Pathion →
Trigintaduoionion.  Layers indexed by the CD doubling.

`theory/math/sym3_spine.md` — Sym(3) 8-fold decomposition
appears across CD layers and Thurston geometries (Part V).
The same decomposition reaches into the eventual physics
deployment (gauge sector) but that side is out of scope
here.

### IV.4 Real213

`theory/math/real213.md` (57 files in `lean/E213/Lib/Math/
Real213/`).  Cuts of P-orbit pairs, parameterised by a
modulus.  No Cauchy sequences; no ε-δ.  The modulus replaces
existential quantification.

`theory/math/modulus.md` — the modulus is an explicit
`Nat → Nat` function; replaces `∀ ε > 0, ∃ N, …` with
constructive `f` such that `n ≥ f(k)` implies the property at
resolution `k`.

### IV.5 Padic

`theory/math/padic_real213.md` — 213-native p-adic numbers
for arbitrary prime `p`.  `ZpSeq`, Hensel lifting (existence +
uniqueness), Teichmüller iteration, ℚ_p, full ultrametric.

5-adic specifically anchors DRLT (the resolution constant
`N_U = 5^25` is a count-Lens output, per
`seed/RESOLUTION_LIMIT_SPEC.md`).

### IV.6 Cauchy, Modulus, FSM

  · `theory/math/cauchy.md` — Cauchy / Euler / Wallis / Pell
    sequences
  · `theory/math/dyadic_fsm.md` — 101 files; Pell-Pisano /
    Tribonacci / Legendre classification via finite-state
    machines
  · `theory/math/cascade_calculus.md` — cascade locality /
    aggregation

---

## Part V — Algebraic and cohomological structure

### V.1 K_{NS, NT}^{(c)} classification — the five-direction c-counter

`theory/math/cohomology/k_nm_c_classification.md` is the
central chapter.  The c-counter programme decomposes into five
independent closure routes, each ∅-axiom:

  · **A — `codim ≥ c` parametric**.  `V33EnrichedParametric`
    proves the lower bound for every `(NS, NT, c)`.  The
    `9 · m` offset cancellation in `NatBeqHelpers` absorbs
    280+ proof sites across 12 templates (L1 parametric
    consolidation, per Part VIII.4).
  · **B — `codim ≤ c` unconditional**.  Closed via 8 explicit
    primary cup generators at `c = 1` plus layer-promotion
    (`promote_face` / `promote_edge`) lifting to ∀c.  The
    `cong` constructor (closure under pointwise equality)
    bridges function-vs-pointwise without `funext`.  See
    `essays/per_layer_completeness_constructive_closure.md`.
  · **C — ψ-discriminator joint kernel ⊆ InPrimary**.
    `V33EnrichedParametricDualSpan*` — the c-many
    ψ-discriminators *span* the dual of H²_enr; PRIMARY
    cup-image rather than FULL is the maximal kill-preserving
    restriction.
  · **D — mediant cohomology functor**.  V/E/F Vandermonde
    counts under Stern-Brocot; `K_{4, 3} = K_{1, 1} ⊕ K_{3, 2}`
    as the marquee identity.  `MediantCohomologyFunctor.
    mediant_cohomology_functor_capstone`.
  · **E — c-counter master**.
    `EnrichedKNSNTcMaster.master_Knn_c_counter_resolved`
    consolidates A–D.

Companion essays:
`essays/c_counter_programme_closure.md` (5-direction synthesis),
`essays/synthesis_interlock_map.md` (parallel with P-orbit's
6-phase closure), `essays/layer_multiplication_pattern.md`
(the shared proof-shape: invariant + offset + cancellation).

**Cross-graph universality**.
`Cohomology/CrossGraphPattern.lean` + `K33Unified.lean` — the
"face-sum-to-zero" identity on 4-cycles at `NT = 3` is
universal across `K_{3, 3}` and `K_{4, 3}`, independent of
`NS`.

### V.2 Stern-Brocot mediant cohomology functor

`theory/math/cohomology/mediant_cohomology_functor.md` — V/E/F
Vandermonde counts under mediant; K_{4, 3} = K_{1, 1} ⊕ K_{3, 2}
as the marquee identity.

### V.3 Tripartite self-containment

`theory/math/cohomology/tripartite_self_containment.md` —
K_{2, 1, 3} cohomology (Betti = (1, 0, 0)) and K_{3, 2}^{(c=2)}'s
local (2, 1, 3) signature at every point.  Cross-frame verdict:
atomic-level duality preserved (|E| = |Δ| = 6), cohomology-level
duality broken (b₁ = 8 ≠ 0).

### V.4 Hodge conjecture programme

`theory/math/cohomology/hodge_conjecture.md` — 67 files, 6
layers (Foundation / Structure / Pairing / Refinement / Toolkit
/ Bridge / MotivicBridge).  Hodge involution ↔ universe-chain
self-pointing.

### V.5 Cohomology family

`theory/math/cohomology/{cochain, cup, cupaw, delta, bipartite,
fractal, aurifeuillean, hodge, surfaces, universal, examples,
bridge}.md` — 12 sub-clusters under cohomology.

### V.6 Sym(3) spine cross-frame

`theory/math/sym3_spine.md` — `2 · trivial ⊕ 3 · standard`
Sym(3)-decomposition appears in K_{3, 2}^{(c=2)} H¹, in
Thurston's 8 geometries, in the Akbulut cork.  Same
decomposition, three independent math frames.  (A fourth
frame — gauge content — surfaces in the eventual physics
side; out of scope here.)  Capstone:
`X1_sym3_cross_frame_capstone`.

### V.7 Universe chain

`theory/math/universe_chain.md` — UniverseChain + Mobius213 +
Nat213 (~32 files).  The chain of universes is forced by P-orbit
iteration.

### V.8 ParadigmDomain — 9-domain unification

`lean/E213/Lib/Math/ParadigmDomain*.lean` — typeclass
formalising that all 9 classical domains (Combinatorics,
Probability, Information, Logic, Topology, Multivariable
Calculus, Complex Analysis, Measure Theory, Cohomology) share
**`truncation_grade = 5 = d`** and decidable Bool atoms.
`uniform_paradigm_witnesses` consolidates them.

The 9 domains are not chosen by historical convention — they
are exactly the natural sub-categories under the
`(NS, NT, d) = (3, 2, 5)` atomic data, each reading the same
truncation through its discipline-specific vocabulary.

`ParadigmDomainGradedRing.lean` lifts the unified typeclass
to a graded-ring structure; `paradigm_coeffs` is the binomial
row of P (Pascal's row 5: `(1, 5, 10, 10, 5, 1)`).

### V.9 Algebra213 / Ring213 / HurwitzRing

`lean/E213/Lib/Math/Tactic/{HurwitzRing, IntSquare,
QuadExtension}.lean` — 213-native polynomial identities for
Cayley-Dickson layers without `propext`.  Hurwitz norm
identity, associativity at each CD level, quadratic-extension
algebra.

`theory/math/algebra213_meta_theorems.md` — the meta-theorems
for the Ring213 / StarRing213 / CDDouble functor tower.  This
is the algebraic substrate that makes the CD construction
PURE through every layer.

### V.10 Aurifeuillean fractal — `N_U + 1`

`theory/math/cohomology/aurifeuillean.md` +
`lean/E213/Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean*.lean`
— the `N_U + 1` family `d^(d^n) + 1` admits a uniform
Aurifeuillean factorisation through `Φ_10(5) = 521` via the
`ℤ[√5]`-norm identity.  16 PURE theorems close the
cyclotomic-cohomology bridge.

The fractal `N_U = 5^25` (count-Lens output at level 2) is
not isolated — `N_U + 1` carries the Aurifeuillean cyclotomic
structure, providing algebraic-geometric anchoring at every
fractal turn.

### V.11 H³, H⁴ stable at +6

`theory/math/exotic_4mfd_cork.md` + `H3Twist.lean` — the
3-skeleton and 4-skeleton truncations stabilise the signed
cork-twist count at `+6` (H¹ = +4, H² = +2, H³ = 0, H⁴ = 0).
The 4-simplex closure of the `K_{3, 2}^{(c=2)} ↪ Δ⁴` dual
filling.

---

## Part VI — GRA universality (Phases 1–22)

GRA — Graded Residue Arithmetic — is the *universal meta-
structure* of 213: the (2, 3)-graded arithmetic forced by
`gcd(NT, NS) = gcd(2, 3) = 1`.  See `theory/math/gra_book.md`
for the textbook treatment, including (post-consolidation)
the master statement, the algebraic-tower / dimensional-
proliferation / Adelic frontiers (Ch. 8–9).

### VI.1 The 7 axioms — Phase 1

A `GRAModel` (`lean/E213/Lib/Math/GRA/GRAModel.lean`) has:

  · A1: two coprime generators `gen1 < gen2`
  · A2: `grade(a ⊕ b) = grade(a) + grade(b)`
  · A3: `grade(a ⊗ b) ≤ grade(a) + grade(b)`
  · A4: universal reachability `∀ n ≥ gen1, ∃ a b, n = gen1·a + gen2·b`
  · A5: depth = ⌈n / gen2⌉
  · A6: greedy optimality
  · A7: Lens universality

`ax_coprime := gcd213 2 3 = 1` (PURE via `gcd213`, not
Lean-core `Nat.gcd`).

### VI.2 Common — the shared PURE arithmetic

`lean/E213/Lib/Math/GRA/Common.lean` — `coprime_2_3`,
`reach_23`, `depth_formula`, `ceil3_le_ceil2` — all PURE, all
the 5 Readings share these.

### VI.3 Five Readings — Phases 1–5

Each Reading is a `GRAModel` instance:

  · R₁ Cohomology — cup-grade, K_{3, 2}^{(c=2)} cochains
  · R₂ Higher Algebra — E_n operad level
  · R₃ HoTT — truncation level
  · R₄ Graph — walk length on K_{3, 2}
  · R₅ Analysis — resolution shift exponent

`gra_universality_witness` proves all five pairwise GRAIso via
the NT hub.

### VI.4 Translation programme — Phase 6

`lean/E213/Lib/Math/GRA/Translation.lean` —
`master_translation_from_any` shows any depth-property holds
in all 5 Readings; `graph_distance_implies_cup_length` etc.
demonstrate "Langlands-style" translation.  Universal depth
comparison `⌈n/3⌉ ≤ (n+1)/2` proved once, valid in all 5.

### VI.5 Category theory — Phases 7–11

  · `Category.lean` — 213-native `Cat` typeclass + `GRACat` +
    `ReadingCat` (connected groupoid)
  · `Groupoid.lean` — every `GRAIso` invertible; `ConnectedHub`
  · `Hom.lean` — `GRAHom` (more general than iso) +
    `isoToHom` forgetful
  · `DepthFunctor.lean` — depth as constant functor on
    `ReadingCat`

### VI.6 Bipartite enrichment + naturality + monoidal — Phases 11–15

  · `Enrichment.lean` — the unified `BipartiteCarrier` enrichment
    (a `Nat` tagged with `n = 0 ∨ n ≥ 2`).  `GRA23_Bipartite` is
    the enriched (2, 3)-GRA model; the canonical `forgetHom :
    GRA23_Bipartite → GRA23_NT` projects to the simplified
    Reading.  The five domain flavours (Walk-length / Cochain-
    degree / Truncation-level / Operad-level / Resolution-
    exponent) are commentary — the math is one structure.
  · `Naturality.lean` — translation between enriched and
    simplified as natural transformation; `DepthNaturality`
    captures depth-preservation.
  · `SectionRetraction.lean` — the forgetful has a section on
    its valid image (`0 ∨ ≥ 2`); `BipartiteRetract` packages
    the retract data.
  · `Monoidal.lean` — `product M₁ M₂` is the monoidal product;
    `trivial23` is unit; unit isos `leftUnitHom` / `rightUnitHom`.

### VI.7 Lens bridge + universal property — Phases 16–18

  · `LensBridge.lean` — `canonicalGradeMap := Raw.fold 2 3 (· + ·)`;
    `bipartiteGradeMap` is `rfl`-equal to it.
  · `CarrierRealization.lean` — `canonical_ge_2` enables direct
    `bipartiteRealize : Raw → BipartiteCarrier` construction at
    the carrier level, bypassing `Raw.fold_slash`'s `combine_sym`
    requirement.
  · `Universality23.lean` — `canonicalGradeMap_universal`:
    any (2, 3)-profile function = `canonicalGradeMap` pointwise

### VI.8 Universe lifting + iso-symmetric combine — Phases 19–21 (unified)

  · `HasDistinguishing213.lean` — unified universe-polymorphic
    typeclass `HasDistinguishing213.{u, v} α`.  Two closed
    instances: `liftedReadingHasDistinguishing213` (strict case,
    `Equiv := Eq`, `Type 1` via ULift) and
    `gra23HasDistinguishing213` (categorical case,
    `Equiv := GRAIso`, monoidal product as combine,
    `productSwapIso` as combine_sym, `trivial23_not_iso_NT` as
    categorical distinctness).  Subsumes the former
    `HasDistinguishingU`, `HasDistinguishingW`,
    `HasDistinguishingWFull` variants from the marathon.

### VI.9 Lens.Unified × GRA capstone — Phase 22

`LensIsoCapstone.lean` — the deepest 213-native statement.

`gradeLens : Lens Nat := ⟨2, 3, (· + ·)⟩`.  By definitional
unfolding `gradeLens.view = canonicalGradeMap`.  Phase 18's
universal property lifts to Lens vocabulary; every
(2, 3)-profile Lens on Nat is `Lens.Unified.LensIso` to
`gradeLens`.

The (2, 3)-arithmetic forced by atomic distinguishing IS a
single `LensIso`-equivalence class — Cat, HoTT, Cochain, Walk,
Resolution, Operad all name the same Lens-kernel on Raw.

**Status**: 22 files, ~3500 lines, **all PURE / 0 DIRTY** —
3 exploratory `HasDistinguishing` variants unified into
`HasDistinguishing213.lean`; 5 domain-flavoured enrichments
(Walk / Cochain / HoTT / HigherAlgebra / Analysis) unified into
one `Enrichment.lean` (`BipartiteCarrier`).

---

## Part VII — Foundational frameworks as Readings

This part is the conceptual capstone.  Per `seed/AXIOM/07_primacy.md`,
every framework is a Lens reading of Raw.  Lean exhibits this
concretely.

### VII.1 Peano as Lens composition

`lean/E213/Lib/Math/AxiomSystems/PeanoAsLensComposition.lean`
— Peano arithmetic *is* a Lens composition over Raw.  The
"successor" axiom is `Raw.slash`-with-`Raw.b` structurally.
No external Peano postulate needed.

### VII.2 ZFC extensionality as Lens

`lean/E213/Lib/Math/AxiomSystems/ZFCExtensionalityAsLens.lean`
— ZFC's extensionality reads as a particular Lens kernel on
Raw.

### VII.3 Classical analysis completeness as Lens

`lean/E213/Lib/Math/AxiomSystems/ClassicalAnalysisCompletenessAsLens.lean`
— LUB property is a Lens kernel; the modulus replaces ε-δ
(per `theory/math/modulus.md`).

### VII.4 Cross-theory cohabit

`lean/E213/Lib/Math/AxiomSystems/CrossTheoryCohabit.lean` —
multiple frameworks cohabit a single Raw via different Lenses.
No framework is privileged; each reads off the same residue
through its chart.

### VII.5 HoTT as a Reading (Phase 12.2 / 22)

`lean/E213/Lib/Math/GRA/HoTTEnrichment.lean` + `LensIsoCapstone`
make this explicit.  HoTT's truncation hierarchy is the R₃
Reading of GRA; combined with Phase 22, HoTT's grade structure
on Raw is `LensIso` to `gradeLens`.

### VII.6 Category theory as a Reading (Phase 7 + 22)

Phase 7's `GRACat` is itself a `Cat`; Phase 22 puts the GRA
grade structure on Raw in the LensIso class with `gradeLens`.
Combined with Phase 20's symmetric monoidal structure
(`productSwapIso`), Cat at the (2, 3)-graded level is a
Reading.

### VII.7 The capstone framing

Per the essay `theory/essays/gra_as_substrate_of_cat_hott.md`:

> The (2, 3)-arithmetic forced by atomic distinguishing IS what
> Category theory and HoTT name when their grade structure is
> brought to the surface.  The conventional precedence
> "GRA-as-structure-inside-Cat/HoTT" inverts the forcing
> direction.  Cat / HoTT carry external design choices
> (universe, ∞-cat doctrine); GRA is forced from atomic
> distinguishing without choice.  Hence GRA → Cat/HoTT in the
> forcing chain, not the reverse.

The full Lean realisation is Phases 17–22 (carrier realization,
universal property, universe lifting, iso-symmetric combine,
full categorical instance, LensIso class).

---

## Part VIII — Methodology and discipline

### VIII.1 Three-tier discipline

`theory/PROMOTION_CRITERIA.md` is canonical.

  · **Tier 1** — `research-notes/` (volatile scratchpad)
  · **Tier 2** — `lean/E213/` (source of truth, PURE-verified)
  · **Tier 3** — `theory/` (narrative, mirrors `lean/E213/Lib/`)

Promotion is on closure: a Lean sub-tree closes (H1–H4 hard
criteria + S1–S3 soft) → narrative chapter at
`theory/<mirror-path>` → source notes archived.

### VIII.2 Strict ∅-axiom standard

`STRICT_ZERO_AXIOM.md` is the live PURE / DIRTY catalog.

Standard target: `#print axioms <thm>` returns "does not depend
on any axioms".  No `propext`, `Quot.sound`, `Classical.choice`,
`Lean.ofReduceBool` (native_decide), `sorryAx`.

Sealed-by-design exceptions:
  · `propext` in `Lens.SemanticAtom` (Prop-as-distinguishing
    thesis)
  · `Quot.sound` in `Lens.Universal/QuotLens` (funext-by-design
    on function-valued combines)

Tier 5.1 (omega → kernel-lemma migration) closed for `Lib/Math/GRA/`
in this session; 401 PURE / 0 DIRTY.

### VIII.3 Scanner suite

`theory/meta/scanner_suite.md` — `seed/THEOREM_METHODOLOGY_SUITE.md`
TH-1 proof-shape fingerprint + the scanner archetypes
(`seed/META_SCAN_ARCHETYPES.md` 11 archetypes).

Tools:
  · `tools/scan_axioms.py` — per-theorem PURE/DIRTY
  · `tools/scan_all_axioms.py` — bulk audit
  · `tools/scan_*.py` — pattern-specific scanners

### VIII.4 Raw-derivation levels

`theory/meta/raw_derivation_levels.md` —
`seed/THEOREM_METHODOLOGY_SUITE.md` TH-2 reading.  Three Levels:

  · **L1** — Raw-internal (Raw vocabulary only)
  · **L2** — Lens-internal (any α-side reading)
  · **L3** — Lens-external (multiple Lenses + Raw)

Each result has a canonical level placement.

### VIII.5 Closed-form spec

`seed/CLOSED_FORM_SPEC.md` — DRLT Closure Form:
> Every K_{3,2}^{(c=2)} observable factors as
> R(NS, NT, d, c) · Π (1 + κ · αⁿ)
> with κ ∈ {natural rationals from L(k)} and n ∈ {GRA grades}.

Bishop subsumption + 3-domain projection catalogue + cross-domain
bridges.

**Propext-avoidance pattern set** (12 patterns).  When a
session hits a `propext` leak during theorem development,
consult the trick set in order:

  1. `rw` via `Iff.trans` instead of `simp` on Iff
  2. term-mode `▸` (Eq.rec) instead of `rw` at goal
  3. `Bool.and_eq_true` direct helpers instead of `decide_eq_true_iff`
  4. Nat-core PURE lemmas (`Nat.add_comm`, `Nat.mul_succ`,
     `Nat.add_assoc`) instead of `omega`
  5. `decide_eq_true_iff` two-direction split
  6. Nat-subtraction PURE alternative
     (`Nat.add_sub_cancel`-style)
  7. `max` / `min` PURE (project's own `max_comm_pure`)
  8. List operations PURE (custom recursion not `simp`)
  9. `by_cases` + explicit case `rfl` instead of `simp [h]`
  10. `obtain` + `.proj` instead of `simp` on conjunctions
  11. structural induction on enumerated finite types
      (`cases r <;> rfl` for `Reading`-style enums)
  12. Tier 5.1 omega → kernel-Nat-lemma migration
      (the Tier 5.1 backlog migration pattern from GRA Phase 1)

### VIII.6 Pattern Catalog — atomic games

`lean/E213/Lib/Math/PatternCatalog/*.lean` formalises four
atomic abstraction games:

  · **Locality** — proof-shape locality (atomic moves)
  · **Typeclass** — typeclass extraction (abstraction via
    interface)
  · **Catamorphism** — `Raw.fold` / `Raw.rec` pattern
  · **Dynamical** — orbit / iteration patterns

Plus the composite games:
  · `Lens = Typeclass × Cata` with compatibility witness
  · `CataForcedForm` for forced catamorphic instances
  · 4 + 6 = 10 distinct patterns total

This is the *methodology counterpart* of GRA Phase 12's five
Readings — at the proof level rather than the data level.

### VIII.7 Proof-shape fingerprinting + parametric extraction

`seed/THEOREM_METHODOLOGY_SUITE.md` §TH-1 + §TH-4 — the
proof-fingerprint suite at four levels:

  · tactic token sequence (most surface)
  · `Expr`-node shape (medium)
  · recursor invocation set (deeper)
  · citation graph (deepest)

When N proofs share byte-identical fingerprint across
independent scanners, **extract the shared implicit lemma**
(L1 parametric consolidation).  Example:
`9 · m` offset cancellation in `NatBeqHelpers` absorbs 280+
sites across 12 templates.

### VIII.8 Falsifiability operationalised

`seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3 — 135 auto-
discovered structural falsifier theorems (negation-shape,
`decide`-verified).  Distribution:

  · 78% are `≠` (e.g., `Raw.a ≠ Raw.b`)
  · 15% general `¬ P`
  · 6% `¬ ∃`
  · 1% `¬ ∀`

Plus 26 physical falsifiers in
`catalogs/falsifier-roster.md`.  Together they form the
measurable validation surface — the *witnesses that 213
forbids certain constructions*.

### VIII.9 Scanner suite (continued)

`seed/META_SCAN_ARCHETYPES.md` enumerates 11 reusable scanner
archetypes (Tier-2 AST motif scanners, Tier-1 syntax-skeleton
scanners, citation-graph analysis, structural-classifier
template, etc.).  Re-use before writing new tooling.

### VIII.6 Failure modes (CLAUDE.md catalog)

12 recurring slips (see CLAUDE.md "Failure modes catalog"):

  · Importing dichotomy
  · Stereotype matching
  · External classification
  · Metaphysical framing
  · Self-soothing agreement
  · Substrate metaphor — most common
  · Count-Lens import as Raw
  · Deferred ontology dichotomy
  · Fine-tuning as forbidden
  · Legacy-deletion narration
  · Universe-constant framing
  · Tier mismatch
  · Equivalence-pluralism

The catalog is the immune system.  Internalise; don't apologise.

---

## Appendices

### A — Lean source map

| Layer | Path | Description |
|---|---|---|
| Theory | `lean/E213/Theory/` | Raw, atomicity, six-theorem |
| Lens | `lean/E213/Lens/` | Lens API, SemanticAtom, Unified |
| Meta | `lean/E213/Meta/` | Tactics, Nat helpers, AxiomMinimality |
| Lib/Math | `lean/E213/Lib/Math/` | All 213-native math (~38 sub-clusters) |
| Lib/Physics | `lean/E213/Lib/Physics/` | All 213-native physics (~13 sub-clusters) |

Architectural canonical: `lean/E213/ARCHITECTURE.md`.

### B — Notation

`seed/NOTATION.md` — symbol conventions.

  · `NS = 3`, `NT = 2`, `d = NS + NT = 5`, `c = 2`
  · `P = [[2, 1], [1, 1]]`, `T(x) = (2x + 1)/(x + 1)`
  · `K_{NS, NT}^{(c)}` — bipartite multigraph; canonical is
    `K_{3, 2}^{(c=2)}`
  · `Δⁿ` — n-simplex on (n + 1) vertices; `Δ⁴` paired with
    `K_{3, 2}^{(c=2)}`
  · `Raw` (213's substrate, lowercase r in narrative)
  · `gcd(NT, NS) = 1` and `Frobenius(2, 3) = 1` — the
    coprimality fact that forces (2, 3)-GRA reachability

### C — Glossary

| Term | 213-native meaning |
|---|---|
| **Raw** | The residue of pointing; free magma on 2 atoms with `slash_comm` |
| **Lens** | Codomain-side shape Raw's fold imposes on α |
| **Lens-arrow** | `Lens.refines L M` — the single concept underlying eq-relation / equiv-class / iso / hom |
| **Distinguishing** | The primitive act 213 names (per `seed/AXIOM/01_residue.md`) |
| **Atom** | `Raw.a` or `Raw.b` |
| **Atomicity** | Pell-Lucas-Möbius forcing of `(NS, NT, c, d) = (3, 2, 2, 5)` |
| **(NS, NT, c, d)** | `(3, 2, 2, 5)` — uniquely forced |
| **K_{NS, NT}^{(c)}** | Canonical bipartite multigraph; `K_{3, 2}^{(c=2)}` is the unique 213-canonical |
| **Δⁿ** | n-simplex; `Δ⁴` is the (c=2) dual filling |
| **Möbius P** | `[[2, 1], [1, 1]]` — the algebraic crystallisation of atomic data |
| **N_U** | `d^(d²) = 5²⁵` — count-Lens output at fractal level 2 |
| **Cup-ring** | Cochain cup-product structure; closure form for K_{3, 2}^{(c=2)} observables |
| **Modulus** | Explicit `Nat → Nat` replacing ε-δ existentials |
| **∅-axiom (PURE)** | `#print axioms` returns empty; no `propext`, `Classical`, native_decide |
| **Closure Form** | `R(NS, NT, d, c) · Π (1 + κ·αⁿ)` decomposition for every K_{3,2}^{(c=2)} observable |
| **GRA** | Graded Residue Arithmetic — the (2, 3)-arithmetic forced by `gcd(NT, NS) = 1` |
| **Reading** | Surface vocabulary on the same (2, 3)-arithmetic (5 + open) |
| **`canonicalGradeMap`** | `Raw.fold 2 3 (· + ·) : Raw → Nat` — the canonical Raw-level (2, 3)-arithmetic |
| **`gradeLens`** | `Lens Nat := ⟨2, 3, (· + ·)⟩` — the Lens whose view is `canonicalGradeMap` |
| **`LensIso`-class of (2, 3)** | The equivalence class of `gradeLens` under `Lens.Unified.LensIso` — GRA's content |

### D — Companion documents

  · `STATE.md` — current state of the framework (closed
    programmes, open frontiers)
  · `RESEARCH_PLAN.md` — ranked roadmap (5 tiers)
  · `STRICT_ZERO_AXIOM.md` — live PURE catalog
  · `HANDOFF.md` — session-state file (volatile)
  · `theory/INDEX.md` — chapter catalog (148 chapters)
  · `theory/essays/INDEX.md` — cross-cutting essays (24+)
  · `seed/INDEX.md` — axiom corpus entry
  · `seed/AXIOM/INDEX.md` — per-clause chapter index
  · `seed/NOTATION.md` — symbol conventions
  · `seed/THEOREM_METHODOLOGY_SUITE.md` — TH-1 through TH-4
  · `seed/META_SCAN_ARCHETYPES.md` — scanner archetypes
  · `seed/CLOSED_FORM_SPEC.md` — DRLT Closure Form

### E — Reading paths

**For first-time readers**:
Part 0 → I (1, 2, 4, 5) → II (1–3) → III.1 → VI.1–VI.3 (skip
proofs)

**For Claude session starts** (per CLAUDE.md):
`seed/AXIOM/05_no_exterior.md` §5 + §8.4 → `research-notes/G29_residue.md`
→ HANDOFF.md → this book's Part 0

**For the (2, 3)-arithmetic capstone**:
Part VI in full + `theory/essays/gra_as_substrate_of_cat_hott.md`
+ `theory/essays/gra_universality_one_principle.md`

**For audit / verification**:
Part VIII → `STRICT_ZERO_AXIOM.md` → `tools/scan_axioms.py`

---

## Versioning

  · **v1** (2026-05-28) — initial linearisation of theory/
    catalog + Lean docstring sweep.  Phases 1–22 of GRA
    consolidated.  Mathematics-only scope.  Status: stable v1.

A *physics-deployment* part will be added once the
mathematical derivation programme closes completely.  Until
then this book stops at Part VIII (Methodology).

Future versions of the mathematics-only book:
  · Pull additional content from Lean docstrings not yet
    surfaced in theory/
  · Expand Part VII as more Foundational-as-Reading
    formalisations close
  · Annotate Tier 5.1 propext-unsealing migrations as they
    land

Closing note: this book is *itself* a Lens reading — the
narrative shape Raw's residue acquires when projected through
the "ordered exposition" chart.  Per
`seed/AXIOM/05_no_exterior.md` §5.1, it is not above the
framework; it is a chart of it.
