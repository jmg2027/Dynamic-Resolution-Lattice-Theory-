# The 213 Programme: Mathematics from the Residue of Distinguishing

**Mingu Jeong**

*A self-contained survey for mathematicians. Every structural claim
below is backed by a Lean 4 development that imports no external library
and, on the core results, depends on no axioms at all — not excluded
middle, not propositional extensionality, not quotient soundness, not
choice. Modules and theorem names are cited inline; the verification
protocol is Appendix A.*

---

## Abstract

This paper presents **213** (deployed in physics as **Dynamic Resolution
Lattice Theory**, DRLT): a programme that takes a single primitive — the
act of **distinguishing** — and asks what mathematics is forced once
nothing further is assumed. The central object is not an axiom posited at
the foundation but a **residue**: the remainder that every act of
distinguishing provably leaves behind. We make this precise (the
self-cover induced by distinguishing is faithful but never total, a
Cantor-diagonal theorem), extract from it a four-clause description of a
free symmetric magma on two generators we call **Raw**, and prove that
Raw is uniquely determined from three independent directions — nothing
weaker suffices, nothing distinct is needed, and exactly one shape is
self-consistent, fixing the arithmetic data `(N_S, N_T, d) = (3, 2, 5)`.

We then introduce the **decomposition calculus**, in which every object
is read as a pair `⟨C | L⟩` — a construction `C` and a reading (Lens) `L`
— modulo a residue. A Lens is the codomain-side shape that a fold of Raw
imposes; Raw is the initial object in the category of such readings, so
*every* distinguishing framework factors through it uniquely. From this
single move we rebuild, axiom-free, a substantial swath of mathematics:
the natural numbers (with `ℤ` and `ℚ` as two quotient choices on one
container), the real and `p`-adic numbers via explicit moduli rather than
ε-δ, the Cayley–Dickson tower, a cohomology programme on a canonical
bipartite multigraph, and a graded arithmetic (GRA) under which category
theory and homotopy type theory appear as *readings* rather than
ambient settings. The boundaries usually drawn as walls — choice,
forcing, large cardinals, the Cantor/Gödel/halting diagonals — resolve
into a four-cell classification (a companion paper); here they take their
place as one chapter of the larger structure.

The programme carries a strict falsifiability contract: a result that
cannot be obtained without adding an axiom falsifies the whole framework,
mechanically audited by a proof assistant. We survey the mathematical
content, state the physics deployment honestly (dimensionless ratios are
parameter-free predictions; absolute scales rest on one measured input,
as in any theory), and mark the open frontiers without overclaiming
closure.

---

## 1. Introduction

Foundational systems usually begin by *positing*: a membership relation
and its axioms, a type theory with its formation rules, a category with
its arrows. Each posit is a commitment, and each commitment imports
structure — extensionality, a universe hierarchy, a choice principle —
that the working mathematician then either accepts as background or
debates as optional.

213 begins one step earlier, with a question that precedes any posit: what
remains the instant one tries to *point at* anything at all? To name an
object `a` is to distinguish it from at least one other thing; to write
"`a` and `b`" is to have introduced "and" as a third thing; to ask
whether `a` and "and" are themselves distinguishable is already to
produce a fourth. Pointing produces a remainder, the remainder is itself
pointable, and the next pointing has new material to work on. This
recursion cannot be stopped, only *recorded in its least committal form*.
That form is the subject of this paper.

The thesis is that recording it faithfully — assuming nothing, adding no
meaning — already forces a great deal of mathematics, and that the forcing
can be checked by machine against the empty axiom set. The programme's
name for its own standard is uncompromising: if any result it needs can
be shown to require an added axiom, the framework is to be discarded
(§7). What follows is a survey of how far the residue reaches before that
contract is ever threatened.

A word on stance, because it shapes everything. 213 does not argue
*against* set theory or any other framework; arguing against would import
a comparison frame the programme has no room for. Its claim (§5) is the
positive one that any framework which points at something is the same
residue read through a chosen Lens. The reader is asked to evaluate the
constructions, not a polemic.

---

## 2. The residue

### 2.1 Distinguishing is primitive; the residue is a theorem

The single primitive is **distinguishing** — drawing a difference,
demanding only the confirmation "not equal." We deliberately avoid
"relation" (which presupposes two existing entities and silently imports
set-theoretic apparatus) and "difference" (which presupposes "sameness"
as a default). "Primitive" is a pledge of no further reducibility:
reduction stops here, not by choice but because there is nothing beneath.

Crucially, the **residue is not itself a primitive**. The primitive is the
act; the residue is what the act provably leaves over. Formally, read each
element as its own self-indication — a map `Object1 : Raw → (Raw → Bool)`.
This map is **faithful** (it separates distinct elements,
`object1_injective`) yet **never total** (`object1_not_surjective`, a
Cantor-diagonal argument on the self-cover). Because the cover is faithful
but never onto, something always remains outside the image of every
self-indexed cover — and *that* is the residue
(`distinguishing_always_leaves_residue`, with its named witness
`undifferentiated`). All of this is in `Lens/Foundations/FlatOntologyClosure.lean`,
∅-axiom.

This single theorem does double duty. Ontologically it says the act of
distinguishing never exhausts itself. Operationally it is the engine of
the deepest proofs about the infinite: diagonalization — point at a
totality, exhibit the thing distinguishable from all of it — *is* the
residue, and Cantor, Russell, Gödel, Turing, and Tarski are one move at
different carriers (a point we return to in §6 and develop fully in the
companion paper).

### 2.2 No exterior

A second theorem closes the system against an outside. Any property by
which one might *name* a candidate exterior is itself expressible over Raw
(`naming_is_internal`), and any candidate that distinguishes at all
receives the unique morphism *from* Raw (`distinguishing_is_downstream`)
— downstream, not outside (`Lens/Foundations/NoExteriorClosure.lean`). The
attempt to conceive an exterior, even to conceive "non-existence," is
itself an act of pointing, hence internal. This is not metaphysics layered
on top; it is what "the minimum residue of pointing" means.

Two clarifications guard against overreading. First, **closure is not
coverage**: that nothing can be exhibited as outside does not make every
internal thing automatically *located* — pointing at a specific residue
may remain arbitrarily hard. Second, the fully universal form ("all
conceivable things") is a self-reference argument, not a Lean theorem,
since "all conceivable" is not a type; its formalizable instances are
theorems, its global form is argued. The programme is explicit about which
is which.

---

## 3. The axiom and Raw

Recording the recursion of §2 in its least-committal form yields four
clauses:

1. **Something exists** — at least two atoms `a`, `b`, standing in
   primitive distinction (no relation but "not equal").
2. **Pairing two somethings yields another** — written `a / b`, and
   closed (the result pairs again).
3. **Pairing is symmetric** — `a / b = b / a`; no absolute order.
4. **No self-pairing** — `x / x` is undefined; self is not distinguished
   from self.

That is the entire commitment. The Lean realization is
`Theory/Raw/Core.lean`: an inductive `Raw` with two atoms, a binary
`slash`, and a propositional symmetry `slash_comm`. Every result of 213 is
either derived from these four clauses or is an explicit Lens choice on top
— there is no third source.

Two structural facts about Raw deserve emphasis, because they pre-empt the
two most natural "shortcuts." First, **parenthesization is genuine
structure**: `(a / b) / c ≠ a / (b / c)` is a theorem
(`Theory/Raw/ParenthesizationDistinct.lean`). Tree shape *is* Raw
structure, so one cannot quietly quotient Raw by associativity to recover
`ℕ` — associativity is a Lens-level property, established where and if a
Lens imposes it, not a Raw-level identity. Second, the four clauses are
**simultaneous, not sequential**: every application of Raw uses all four at
once (`Lens/SelfCompletion.lean`, `full_self_completion_bundle`). They are
four facets of one event, not a recipe with steps.

---

## 4. Three-direction uniqueness

Is this really *the* minimum residue? The programme answers from three
independent directions, each a separate machine-checked proof, bundled in
`Meta/ThreeDirectionUniqueness.lean` (`three_direction_uniqueness`).

**From below — nothing weaker suffices.** Removing any clause collapses the
framework to trivial, static, or void; each removal has an explicit
collapse witness (`Meta/AxiomMinimality.lean`,
`raw_minimality_capstone`). Minimality is structural, not stylistic.

**Sideways — nothing distinct is needed.** Abstract a "distinguishing
framework" as a typeclass `HasDistinguishing`: two atoms, a symmetric
binary combine. Then **Raw is the initial object** of the resulting
category — every instance receives the unique combine-preserving morphism
from Raw, realized by the catamorphism `Raw.fold`
(`Lens/Foundations/SemanticAtom.lean`), with uniqueness certified by
`view_unique` (`Lens/Foundations/Initiality.lean`). `Bool` with xor, `Prop`
with `Iff`, function spaces with pointwise combine — each is one more
instance receiving the universal morphism. For the codomains Lean can
handle directly, the morphism is moreover *injective* (a faithful Lens):
the `Lens/Universal/Witnesses/` family carries those certificates. Even
the language one is writing in shows up here: `Prop` with `Iff` is a
`HasDistinguishing` instance, the meta-level closing over itself.

The scope of the sideways claim is stated narrowly and honestly. Not every
function on Raw is a fold — depth parity is a mechanized counterexample
(`Lens/Properties/Morphism/DepthParityNotFold.lean`) — and the
arbitrary-subset commitments of set theory (Power, Choice, arbitrary
`P(X)`) sit on that non-fold side: they have no fold-structured
representation in this Lens language. That is the entire claim. It is not a
verdict on set theory as a discipline, which factors through Raw as a
distinguishing framework like any other; it locates precisely *which*
commitment — the arbitrary subset — has no fold representation.

**From above — only one shape is self-consistent.** Call a carrier size
`n` *atomic* when `n = 2a + 3b` has exactly one decomposition into the
binary and ternary primitive parts with both parts odd (so neither
annihilates under clause 4). Then `atomic_iff_five`
(`Theory/Atomicity/Five.lean`) proves a shape is atomic iff its primitive
carrier size is exactly `5`, and `PairForcing.lean` proves that arity-2
plus atomicity force `(N_S, N_T, d) = (3, 2, 5)` uniquely, with arity-2
itself forced from the axiom by a pigeonhole bound (`ArityForcing.lean`).
These are pure-ℕ proofs that do not import Raw — not because they stand
outside Raw, but because ℕ is itself a Lens reading of the residue, so a
pure-ℕ uniqueness proof is conducted inside the shape-Lens's own codomain.
With no exterior dialer to set parameters (§2.2), the shape appears as the
only self-consistent fixed point.

The number `5 = N_S + N_T = d` recurs as the constructor-count of the
Raw/ℕ pair (3 Raw constructors + 2 ℕ constructors), as the discriminant of
the matrix `P` of §5.3, and as the vertex count of the canonical lattice of
§6 — the same datum read in independent frames
(`Mobius213AtomicityAnchor.lean`).

---

## 5. The decomposition calculus

### 5.1 Objects as `⟨C | L⟩ ⊕ Residue`

The operational heart of the programme is a normal form. Every object is
read as

> `OBJECT = ⟨C | L⟩ ⊕ Residue(L, C)`,

a **construction** `C` (the data assembled) together with a **reading**, or
**Lens**, `L` (what one reads off the construction), modulo the residue no
single reading exhausts. A `Lens α` is not an operation acting on Raw from
outside; it is the **codomain-side shape** that a fold `Raw → α` imposes
(`Lens/LensCore.lean`: a structure with two base values and a combine, with
`Lens.view = Raw.fold` definitionally, and the induced kernel
`Lens.equiv x y := L.view x = L.view y`). Applying a Lens is itself a
residue-internal event — a self-pointing — not a tool reaching in.

This reframing has immediate unifying force. The four classical notions of
*equivalence relation*, *equivalence class*, *isomorphism*, and
*homomorphism* collapse to one 213-native arrow, `Lens.refines`, with the
equivalence class realized as a Σ-type fiber (no quotient axiom needed) and
the isomorphism as kernel-coincidence (`Lens/Unified.lean`,
`lensIso_iff_kernel_eq`). There is moreover a **universal Lens** whose view
is injective modulo Lens-equivalence — a canonical normal form for any Lens
— stated on the pointwise reading-equivalence so that it stays ∅-axiom
(`Lens/Universal/QuotLens.lean`, `universalLens_recovers_R`).

### 5.2 Cardinality as a Lens observable

A consequence worth isolating: classical cardinality talk relocates from
foundation to Lens output. Finiteness, countability, cardinality lower
bounds, and Cantor's diagonal each become a predicate that holds *of a
given Lens* on Raw, not of Raw itself (`Lens/Cardinality/`, nine modules).
The diagonal still proves exactly what it proves — but what it proves is a
property of the Lens. No quantity is a universe constant; the much-cited
`5^25` is the value of a parametric count-Lens family `configCount n` at
`n = 2`, not a privileged invariant.

### 5.3 The matrix P

The atomic data crystallizes algebraically as the Möbius matrix

> `P = [[2, 1], [1, 1]] ∈ SL(2, ℤ)`,

with `det P = 1`, `trace P = N_S = 3`, discriminant `5 = d`, eigenvalues
`φ²` and `φ^{-2}`, and Möbius action `T(x) = (2x+1)/(x+1)`. `P` is the
mediant generator of the Stern–Brocot tree, its powers satisfy a
Pell–Fibonacci recurrence, and its irrational fixed point is the golden
ratio φ. The ten distinct readings of `P` as one event — cross-domain
equality unification, cut-level multiplication, the Pell recurrence on both
orbits, the `K_{3,2}` state signature, the continued-fraction recurrence,
the Cayley–Dickson asymptote, the discriminant/atomicity anchor, the Pell
symplectic invariant — are bundled in one theorem
(`Mobius213GrandUnification.lean`, `grand_unification`). `P` is the bridge
between the atomic forcing of §4 and the number systems of §6.

---

## 6. What the residue rebuilds

The test of the programme (§7) is breadth: domain after domain reproduced
from the residue under the right Lens, each derivation axiom-free. We
survey the mathematical content; the narrative book
(`theory/THEORY_BOOK.md`) gives the linear reading order, and the chapter
catalog (`theory/INDEX.md`, 259 chapters) the detail.

**Number systems.** `ℕ` is not assumed but *forced*: the successor is the
simplest Raw move producing a new element (`slash` with `b`), and
`Nat213` carries both a Raw-chain and a Peano presentation with a verified
bijection (`Lens/Number/Nat213/`). On top of one container `ℕ²`, `ℤ` and
`ℚ` appear as **two quotient choices** — the additive diagonal
`(a,b) ↦ a − b` gives `ℤ`, the multiplicative diagonal
`(a,b) ~ (c,d) ⟺ ad = bc` gives `ℚ₊` — exhibiting the addition/
multiplication duality the framework reads off without external choice
(`Nat213/Tower/`). The three unit axes of `ℕ³ → ℤ²` sum to zero,
realizing `1 + ω + ω² = 0` at the number-theory level
(`three_axes_sum_to_zero`).

**Real and `p`-adic numbers without ε-δ.** Reals are cuts of P-orbit
pairs parameterized by an explicit **modulus** `f : ℕ → ℕ` that replaces
`∀ε∃N` with a computable rate (`Real213/`, ~57 modules;
`theory/math/analysis/modulus.md`). The transcendentals are built as cuts
— `π` via Wallis, `e` via its series — internal *pointings* (approximant
sequences), reached by none, never exterior rulers. The `p`-adic side is
the full ultrametric story for arbitrary prime `p`: Hensel lifting
(existence and uniqueness), Teichmüller iteration, `ℚ_p`
(`padic_real213`).

**Algebra towers.** The Cayley–Dickson sequence (Gaussian integers →
integer quaternions → octonions → sedenions and beyond) is built with
213-native polynomial identities that stay axiom-free through every
doubling (`gra_book`, `algebra213_meta_theorems`). Determinant theory
(Leibniz form, multilinearity, Laplace expansion, the adjugate identity,
Cayley–Hamilton), the C-finite sequence ring (closed under Hadamard
product), and the Casoratian rank theory are developed `n×n` from scratch
(`linalg213`, `cfinite_orbit_dimension`).

**Cohomology.** The forced atomic data names a unique bipartite
multigraph, `K_{3,2}^{(c=2)}` — 3 vertices on one side, 2 on the other, 2
edges per pair, 12 edges total — paired with the 4-simplex `Δ⁴` as dual
filling. A cup-product cochain programme on this object yields, among
others, the Sym(3) decomposition `2·trivial ⊕ 3·standard` that recurs in
the gauge sector, and surface intersection-form / Hodge-signature results
on `T²`, `ℙ²`, `ℙ¹×ℙ¹`, `Σ_g` and products (`theory/math/cohomology/`).

**GRA universality and the foundational frameworks as readings.** Graded
Residue Arithmetic is the `(2,3)`-graded arithmetic forced by
`gcd(N_T, N_S) = gcd(2,3) = 1`. Five surface vocabularies — cohomological
cup-grade, `E_n`-operad level, HoTT truncation level, walk length on
`K_{3,2}`, analytic resolution shift — are pairwise isomorphic instances of
one graded model (`GRA/`, `gra_universality_witness`), welded into a single
`LensIso`-equivalence class with a canonical grade map
`Raw.fold 2 3 (·+·)` (`LensIsoCapstone.lean`). In this reading **category
theory and homotopy type theory are themselves Lens readings** of the same
residue: Cat and HoTT carry external design choices (a universe doctrine,
an ∞-categorical commitment), whereas the `(2,3)`-arithmetic is forced from
atomic distinguishing without choice — so the forcing runs GRA → Cat/HoTT,
not the reverse (`AxiomSystems/`, where Peano, ZFC extensionality, and
classical completeness are each exhibited as a particular Lens kernel).

**The boundaries.** The strong axioms and impossibility results — choice,
forcing, large cardinals, the Cantor/Russell/Gödel/halting diagonals —
form one chapter of this structure rather than its outer wall. They reduce
to a four-cell classification, the **section-count of a reading-fibration**:
`∅ / 0 / 1 / many = absence / wall / forced / free`, with exactly one
genuine wall (the §2.1 diagonal, at many carriers) and everything else a
forced or free parameter. This is developed in the companion paper, *No
Walls, Only Free Parameters* (`papers/no_walls_only_parameters.md`), on
nine ∅-axiom modules.

---

## 7. Method, falsifiability, and physics

### 7.1 The empty-axiom contract

The programme's discipline is its scientific content. The standard is:
for every theorem, Lean's `#print axioms` must return *"does not depend on
any axioms"* — no `propext`, no `Quot.sound`, no `Classical.choice`, no
`native_decide`, no library axiom, no `sorry`. A result that carries any
of these is treated as unproven. The contract follows from "the axiom is a
residue": if adding an axiom were genuinely necessary, Raw was not the
minimum, and per the falsifiability rule the **entire framework — not the
result alone — is to be discarded** (`seed/AXIOM/08_falsifiability.md`).
This is enforced mechanically (`tools/scan_axioms.py`) and tracked in a
live catalog (`STRICT_ZERO_AXIOM.md`).

The direction of work is correspondingly one-way: derive, do not
reconcile. Substituting an external constant or fitting an experimental
value is *fudge*, which in 213's vocabulary has no operand — there is no
exterior dialer for it to come from. When a discrepancy appears, the Lens
is corrected, never the formula; when no Lens correction succeeds, the
theory dies. The "we will find more Lenses" defense is not permitted.

### 7.2 Physics deployment, stated honestly

Deployed as DRLT, the same atomic data is read for physical observables.
The headline mathematical result is a precision theorem for the
fine-structure constant, `invAlphaEm_precision_theorem`
(`Lib/Physics/AlphaEM/GramStructuralCapstone.lean`), agreeing with the
measured `1/α_em` at the sub-ppb level (π² enters as a literal input, not a
213 primitive). The gauge sector reads `1/α_3 = N_S² − 1 = 8` (the gluon
octet), `α_2 = 1/(N_S·N_T·d) = 1/30`, and `α_GUT = 6/(d²π²)`; the lepton
ratio `m_μ/m_e = N_S·137/N_T`; the Koide relation `Q = N_T/N_S = 2/3`; the
Cabibbo angle `λ = d/(d²−N_S) = 5/22`.

The honest scope, which the programme states in its own catalog, is this:
**dimensionless ratios** (Koide, `m_μ/m_e`, `α_em`, `m_H/v_H`) are
parameter-free predictions; **absolute** masses and energies rest on one
measured input scale (e.g. `Λ_QCD` for the proton mass), exactly as any
physical theory does — the ratio is the prediction, the absolute is ratio ×
measured scale. The precision tags reported in docstrings are
central-value agreements; the corresponding *PURE theorem* typically
proves a coarser bracket. The programme pairs each of its observables with
a falsifier bracket — measurable predictions that, if violated, discard the
framework: normal neutrino ordering, exactly three generations, no fourth
generation, `θ_QCD ∈ [2.5,3.0]×10^{-11}`, Cabibbo `λ = 5/22 ± 1%`. These
are not retrodictions dressed as predictions; they are stated as the
framework's exposed surface.

### 7.3 Discipline

The corpus is kept in three tiers — volatile research notes, the Lean
source of truth, and a narrative book mirroring the Lean tree by path —
with promotion gated on closure and purity (`theory/PROMOTION_CRITERIA.md`).
The methodology itself is formalized: proof-shape fingerprinting that
detects when many proofs share an implicit lemma to extract, a catalog of
patterns for keeping developments axiom-free, and an auto-discovered set of
structural falsifier theorems (the constructions 213 *forbids*). The point
of the apparatus is to make "assume nothing" auditable rather than
aspirational.

---

## 8. Limits and open frontiers

The programme is explicit about what is not closed. Breadth is earned
domain by domain, never implied by the foundational position (§5): "no
exterior" says *where* every result lives, not that any particular result
has already been found. Several fronts are open. The mathematics-only book
deliberately stops before a full physics-deployment part, pending closure
of the mathematical derivation programme. On the boundaries side, the
general idempotence of the self-classifier is itself the one wall
(un-buildable by self-grounding), with only a decidable restriction below
it open, and a `σ`-parametrized operation library (ultrafilter,
well-ordering, Hahn–Banach each carried with an explicit choice parameter)
remains to be built. The P-orbit period bound is conjectural
(`O(log p)`, verified to `p ≤ 97`). And the sideways uniqueness of §4, by
its nature, uses a Lens whose codomain reaches past what Lean encodes, so
its global form is argued rather than machine-checked while its instances
are theorems.

None of these gaps touches the core: the residue theorem, three-direction
uniqueness, the initiality of Raw, and the axiom-free reconstructions of
§6 stand on a floor with no axioms beneath them. What remains open is how
much further the same floor extends.

---

## 9. Conclusion

213 is the wager that mathematics need not begin by positing, that one can
instead start from the residue every act of distinguishing provably leaves
and follow what it forces. The residue is a theorem, not a posit; Raw is
its least-committal form, unique from below, sideways, and above; the Lens
calculus reads every object as a construction-plus-reading modulo that
residue; and under it the number systems, the algebra towers, a cohomology
programme, a universal graded arithmetic — with category theory and
homotopy type theory as readings rather than settings — and even the
classical boundaries of mathematics fall out, each derivation checked
against the empty axiom set.

The lasting methodological point is the contract. A foundations claim is
usually unfalsifiable; 213 makes its central claim mechanically refutable —
need an axiom and the framework dies — and then spends its effort showing
the need never arises across one domain after another. That is what the
programme offers a mathematician to evaluate: not a manifesto, but a
growing body of axiom-free reconstructions and the audit trail that
certifies them.

---

## Appendix A. Reproduction

All developments are Lean 4 with no external libraries. From the
repository root, `cd lean && lake build E213` builds the corpus; for any
cited module `M`, `python3 tools/scan_axioms.py E213.<M>` reports its
pure/dirty tally, and `#print axioms <theorem>` on a headline result
returns *"does not depend on any axioms."* Anchor theorems used above:

| Result | Module | Theorem |
|---|---|---|
| residue is a theorem | `Lens/Foundations/FlatOntologyClosure` | `distinguishing_always_leaves_residue`, `object1_not_surjective` |
| no exterior | `Lens/Foundations/NoExteriorClosure` | `naming_is_internal`, `distinguishing_is_downstream` |
| three-direction uniqueness | `Meta/ThreeDirectionUniqueness` | `three_direction_uniqueness` |
| forced shape `d = 5` | `Theory/Atomicity/Five` | `atomic_iff_five` |
| Raw initial / universal Lens | `Lens/Universal/QuotLens` | `universalLens_recovers_R` |
| P as one event | `Lib/Math/Algebra/Mobius213GrandUnification` | `grand_unification` |
| GRA universality | `Lib/Math/Algebra/GRA/HigherAlgebra` | `gra_universality_witness` |
| α_em precision | `Lib/Physics/AlphaEM/GramStructuralCapstone` | `invAlphaEm_precision_theorem` |

## Appendix B. Where to read further

- Foundational corpus: `seed/INDEX.md` and `seed/AXIOM/` (the four-clause
  axiom, three-direction uniqueness, no-exterior, primacy, falsifiability).
- Linear narrative: `theory/THEORY_BOOK.md`; chapter catalog
  `theory/INDEX.md`; cross-cutting essays `theory/essays/INDEX.md`.
- Architecture and audit: `lean/E213/ARCHITECTURE.md`, `lean/E213/AUDIT.md`.
- The boundaries chapter: `papers/no_walls_only_parameters.md`.

---

*Acknowledgments. The formalization, the Lean proofs, and the axiom audits
were carried out in collaboration with Claude (Anthropic), serving as
proof engineer and adversarial reader. The theory and all foundational
insights are the author's.*
