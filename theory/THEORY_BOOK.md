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

213 — also called **DRLT** when deployed to physics — is the
4-clause Raw axiom and *everything it forces*:

  · the atomic data `(NS, NT, c, d) = (3, 2, 2, 5)`
  · the Möbius matrix `P = [[2, 1], [1, 1]]` (det 1, trace 3)
  · the (2, 3)-graded arithmetic of GRA
  · the universe of Reading vocabularies (Cat, HoTT, Cohomology,
    Walk, Resolution, Operad, Cochain, Truncation, …)
  · the precision physics — α_em at 0.09 ppb, gluon octet,
    proton mass — as canonical numbers, not fits

This book walks the forcing chain.

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

### I.4 No exterior

`seed/AXIOM/05_no_exterior.md` §5.1 — **no exterior**.  The
framework has no "outside" from which to derive its content.
Self-completion is structural closure, not a deficiency.

§5.4 is the **dichotomy-avoidance guide** — re-read every
session (per CLAUDE.md boot sequence).  Common slips:
"foundation vs derivation," "inside vs outside 213," "classical
vs 213" — all import an exterior the framework rejects.

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

### I.7 Lean correspondence

`seed/AXIOM/09_lean_correspondence.md` formalises the Raw
inductive in Lean 4 and proves three-direction uniqueness as a
faithful emulator.  `lean/E213/AUDIT.md` is the implementation
audit.

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
in the meaning-framework category).

**75 thesis** (`research-notes/75_semantic_atom.md`): "Nothing
with meaning escapes 213."  Lean form: every meaning-framework
α has a `HasDistinguishing` instance, and Raw embeds into it
canonically.

### II.5 Universe-polymorphic version (Phase 19+)

`lean/E213/Lib/Math/GRA/Universe1.lean` —
`HasDistinguishingU.{u}` is the universe-polymorphic parallel,
necessary because `Cat.{0, 0} : Type 1`.  Phase 19 exhibits
`HasDistinguishingU.{1} (ULift.{1, 0} Reading)`.

`HasDistinguishingW.{u, v}` (Phase 20) weakens combine_sym to
hold up to a chosen `Equiv` relation.  Phase 21
(`HasDistinguishingWFull`) adds categorical distinctness.
Together: a `Type 1` carrier (`GRA23`) admits the natural
categorical structure, with monoidal product as combine and
`GRAIso` as equivalence.

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

The point: **`Nat` is not assumed.  `Nat` is forced** —
from Raw + P (the "successor" operation is `slashOrSelf
n Raw.b`, the simplest Raw-level move that produces a
non-trivial new element).

### IV.2 Möbius P and Stern-Brocot

`lean/E213/Lib/Math/Real213/Mobius213{Equiv, SternBrocot,
PellInvariant}.lean` close the chapter:

  · `cutEq ↔ sternBrocotEq ∧ (0, 0)` — equivalence on cuts via
    P-mediant closure
  · P generates the Stern-Brocot tree
  · Pell unit invariant

P is therefore both the *atomic algebraic anchor* (Part III)
and the *equivalence-class structure on cuts* (here).

### IV.3 Cayley-Dickson tower

`theory/math/cayley_dickson/algebra_tower.md` —
ZI (Gaussian integers) → Lipschitz (integer quaternions) →
Cayley (integer octonions) → Sedenion → Pathion →
Trigintaduoionion.  Layers indexed by the CD doubling.

`theory/math/sym3_spine.md` — Sym(3) 8-fold decomposition
appears across CD layers, Thurston geometries (Part V), and
gluon octets (Part VII).

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

### V.1 K_{NS, NT}^{(c)} classification

`theory/math/cohomology/k_nm_c_classification.md` is the
central chapter (this and the next two close the c-counter
programme).

Five directions:

  · A — codim ≥ c (parametric, ∀(NS, NT, c))
  · B — codim ≤ c (per-layer completeness, unconditional via
    8 primary cup generators + `cong` constructor)
  · C — ψ-discriminator joint kernel ⊆ InPrimary
  · D — mediant cohomology functor (Vandermonde under
    Stern-Brocot)
  · E — c-counter master:
    `EnrichedKNSNTcMaster.master_Knn_c_counter_resolved`

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
Thurston's 8 geometries, in the gluon octet, in the Akbulut
cork.  Same decomposition, 4 frames.  Capstone:
`X1_sym3_cross_frame_capstone`.

### V.7 Universe chain

`theory/math/universe_chain.md` — UniverseChain + Mobius213 +
Nat213 (~32 files).  The chain of universes is forced by P-orbit
iteration.

---

## Part VI — GRA universality (Phases 1–22)

GRA — Graded Residue Arithmetic — is the *universal meta-
structure* of 213: the (2, 3)-graded arithmetic forced by
`gcd(NT, NS) = gcd(2, 3) = 1`.  See `theory/math/gra_book.md`
for the textbook treatment, `theory/math/graded_residue_arithmetic.md`
for the synthesis.

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
  · `WalkEnrichment.lean` — first carrier enrichment (R₄)

### VI.6 Enrichments and natural structure — Phases 12–15

  · `CochainEnrichment` + `HoTTEnrichment` +
    `HigherAlgebraEnrichment` + `AnalysisEnrichment` — full
    enrichment for the remaining 4 Readings
  · `Naturality.lean` — translation as natural transformation;
    `DepthNaturality` capstone
  · `SectionRetraction.lean` — forgetful has a section on the
    valid image (`0 ∨ ≥ 2`)
  · `Monoidal.lean` — `product M₁ M₂` is the monoidal product;
    `trivial23` is unit; unit isos `leftUnitHom` / `rightUnitHom`

### VI.7 Lens bridge + universal property — Phases 16–18

  · `LensBridge.lean` — `canonicalGradeMap := Raw.fold 2 3 (· + ·)`;
    all 5 enrichment grade maps reduce to it by `rfl`
  · `CarrierRealization.lean` — `canonical_ge_2` enables direct
    `walkRealize`/etc. construction at the carrier level,
    bypassing `Raw.fold_slash`'s `combine_sym` requirement
  · `Universality23.lean` — `canonicalGradeMap_universal`:
    any (2, 3)-profile function = `canonicalGradeMap` pointwise

### VI.8 Universe lifting + iso-symmetric combine — Phases 19–21

  · `Universe1.lean` — `HasDistinguishingU.{u}` polymorphic;
    `Type 1` instance via `ULift Reading`
  · `HasDistinguishingW.lean` — weakened `combine_sym` up to
    `Equiv` relation; `productSwapIso` braiding
  · `HasDistinguishingWFull.lean` — full instance on `GRA23 :
    Type 1` with categorical distinctness via cardinality
    (`trivial23_not_iso_NT`)

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

**Status**: 28 files, ~4900 lines, **401 PURE / 0 DIRTY**.

---

## Part VII — Physics deployment

### VII.1 Atomic constants

`theory/physics/foundations/atomic_constants.md` — the
canonical chapter.  `(NS, NT, c, d) = (3, 2, 2, 5)` derived
from atomicity + alive + Pell-Lucas + k = 2 arity.

### VII.2 C3 chain and gauge content

`theory/physics/symmetry/c3_chain.md` — Sym(3)-action on
K_{3, 2} forces the gauge content.  `b₁(K_{3, 2}^{(c=2)}) = 8`
matches the gluon octet exactly.

### VII.3 α_em precision

`theory/physics/alpha_em/precision_derivation.md` — α_em at
**0.09 ppb** from the 5-layer Gram structural + cup-ladder +
SO(10) tail decomposition.  Lean: `Physics/AlphaEM/Capstone`.

  · Step 1: Gram structural (`GramStructural`)
  · Step 2: cup-ladder (`KPlus1AlphaPowerGraduation`)
  · Step 3: Newton corrections (`GramStructuralNewton`)
  · Step 4: capstone (`GramStructuralCapstone`)
  · Step 5: SO(10) tail
  · Step 6: K_{3,2}^{(c=2)} higher cohomology (sub-ppb)

Validation Standard #1 met.  Falsifier in `catalogs/falsifier-roster.md`.

### VII.4 Other observables

  · `theory/physics/foundations/proton_electron_ratio.md`
  · `theory/physics/hadron.md` — falsifier brackets; baryon
    spectrum open (Tier 4.2)
  · `theory/physics/cosmology/gravity_shadow.md`
  · …

`theory/physics/INDEX.md` enumerates 18 chapters.

### VII.5 Validation Standard

From `CLAUDE.md`:

> From zero knowledge of existing physics/math, DRLT must
> satisfy at least one of:
>
> 1. Strict ∅-axiom precision theorem at ppb-ppm
> 2. Strict ∅-axiom falsifier — measurable

Below this = below standard.  α_em at 0.09 ppb (Step 6:
sub-ppb) meets #1; `N_gen = 3` and `θ_QCD < J·α⁴` meet #2.

---

## Part VIII — Foundational frameworks as Readings

This part is the conceptual capstone.  Per `seed/AXIOM/07_primacy.md`,
every framework is a Lens reading of Raw.  Lean exhibits this
concretely.

### VIII.1 Peano as Lens composition

`lean/E213/Lib/Math/AxiomSystems/PeanoAsLensComposition.lean`
— Peano arithmetic *is* a Lens composition over Raw.  The
"successor" axiom is `Raw.slash`-with-`Raw.b` structurally.
No external Peano postulate needed.

### VIII.2 ZFC extensionality as Lens

`lean/E213/Lib/Math/AxiomSystems/ZFCExtensionalityAsLens.lean`
— ZFC's extensionality reads as a particular Lens kernel on
Raw.

### VIII.3 Classical analysis completeness as Lens

`lean/E213/Lib/Math/AxiomSystems/ClassicalAnalysisCompletenessAsLens.lean`
— LUB property is a Lens kernel; the modulus replaces ε-δ
(per `theory/math/modulus.md`).

### VIII.4 Cross-theory cohabit

`lean/E213/Lib/Math/AxiomSystems/CrossTheoryCohabit.lean` —
multiple frameworks cohabit a single Raw via different Lenses.
No framework is privileged; each reads off the same residue
through its chart.

### VIII.5 HoTT as a Reading (Phase 12.2 / 22)

`lean/E213/Lib/Math/GRA/HoTTEnrichment.lean` + `LensIsoCapstone`
make this explicit.  HoTT's truncation hierarchy is the R₃
Reading of GRA; combined with Phase 22, HoTT's grade structure
on Raw is `LensIso` to `gradeLens`.

### VIII.6 Category theory as a Reading (Phase 7 + 22)

Phase 7's `GRACat` is itself a `Cat`; Phase 22 puts the GRA
grade structure on Raw in the LensIso class with `gradeLens`.
Combined with Phase 20's symmetric monoidal structure
(`productSwapIso`), Cat at the (2, 3)-graded level is a
Reading.

### VIII.7 The capstone framing

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

## Part IX — Methodology and discipline

### IX.1 Three-tier discipline

`theory/PROMOTION_CRITERIA.md` is canonical.

  · **Tier 1** — `research-notes/` (volatile scratchpad)
  · **Tier 2** — `lean/E213/` (source of truth, PURE-verified)
  · **Tier 3** — `theory/` (narrative, mirrors `lean/E213/Lib/`)

Promotion is on closure: a Lean sub-tree closes (H1–H4 hard
criteria + S1–S3 soft) → narrative chapter at
`theory/<mirror-path>` → source notes archived.

### IX.2 Strict ∅-axiom standard

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

### IX.3 Scanner suite

`theory/meta/scanner_suite.md` — `seed/THEOREM_METHODOLOGY_SUITE.md`
TH-1 proof-shape fingerprint + the scanner archetypes
(`seed/META_SCAN_ARCHETYPES.md` 11 archetypes).

Tools:
  · `tools/scan_axioms.py` — per-theorem PURE/DIRTY
  · `tools/scan_all_axioms.py` — bulk audit
  · `tools/scan_*.py` — pattern-specific scanners

### IX.4 Raw-derivation levels

`theory/meta/raw_derivation_levels.md` —
`seed/THEOREM_METHODOLOGY_SUITE.md` TH-2 reading.  Three Levels:

  · **L1** — Raw-internal (Raw vocabulary only)
  · **L2** — Lens-internal (any α-side reading)
  · **L3** — Lens-external (multiple Lenses + Raw)

Each result has a canonical level placement.

### IX.5 Closed-form spec

`seed/CLOSED_FORM_SPEC.md` — DRLT Closure Form:
> Every K_{3,2}^{(c=2)} observable factors as
> R(NS, NT, d, c) · Π (1 + κ · αⁿ)
> with κ ∈ {natural rationals from L(k)} and n ∈ {GRA grades}.

Bishop subsumption + 3-domain projection catalogue + cross-domain
bridges.

### IX.6 Failure modes (CLAUDE.md catalog)

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
  · `α_em` (electromagnetic fine-structure constant)
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

**For physics deployment**:
Part III → Part VII

**For audit / verification**:
Part IX → `STRICT_ZERO_AXIOM.md` → `tools/scan_axioms.py`

---

## Versioning

  · **v1** (2026-05-28) — initial linearisation of theory/
    catalog + Lean docstring sweep.  Phases 1–22 of GRA
    consolidated.  Status: stable v1.

Future versions:
  · Pull additional content from Lean docstrings not yet
    surfaced in theory/
  · Expand Part VII as physics deployment progresses
  · Expand Part VIII as more Foundational-as-Reading
    formalisations close
  · Annotate Tier 5.1 propext-unsealing migrations as they
    land

Closing note: this book is *itself* a Lens reading — the
narrative shape Raw's residue acquires when projected through
the "ordered exposition" chart.  Per
`seed/AXIOM/05_no_exterior.md` §5.1, it is not above the
framework; it is a chart of it.
