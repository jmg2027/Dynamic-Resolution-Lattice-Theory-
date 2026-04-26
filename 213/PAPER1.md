# 213: A Minimal Foundational System via Raw + Lens

**Author**: Mingu Jeong (Independent Researcher)

**Status**: Lean 4 core formalization (no Mathlib).  0 sorry,
0 external axioms beyond the Lean baseline (`propext`,
`Quot.sound`).  Acknowledgments and contributor attributions
appear in §8.4.

---

## Abstract

We present **213**, a foundational system consisting of two
layers: an inductive type `Raw` with two primitive elements
`a`, `b` and a binary operation `slash` on distinct arguments,
together with a fold-structured observation record `Lens`
representing homomorphisms out of `Raw`.  Every result reported
in this paper is mechanically verified in Lean 4 core, with
axiom budget bounded by `[propext, Quot.sound]`.

The development establishes: (i) strict minimality of the Raw
axiom (each clause is essential, formalized in
`AxiomMinimality.lean`); (ii) initiality of `Raw` in the
category of commutative `Raw`-algebras (`raw_initial`); (iii)
encoding-artifact independence of the canonical-form
comparison (`RawBy_bijection`); (iv) 213-side counterparts of
several ZFC commitments — full reduction of Choice via
`universalLens`, an explicit boundary witness for Power-set
(depth parity is not a Lens kernel), Comprehension as
distinguishing-closed `Subtype`, and Coproduct via `Prism`;
(v) Cauchy completeness exhibited on √2 (Pell), the p-adic
integers ℤ_p (mod-tower), and the transcendentals e (Euler
partial sums) and π/2 (Wallis product), each at explicit
rational thresholds; and (vi) a fifteen-component formal
package supporting the *semantic atom* reading: any type with
two distinguishable elements and a commutative binary operation
is a `HasDistinguishing` instance, with `universalMorphism :
Raw → α` the induced unique homomorphism.

The framework operates under a falsifiability contract: should
any result genuinely require an axiom beyond the Lean baseline,
the theory is to be discarded.  No such addition has been
required.

---

## §1 Introduction

### §1.1 The framework

The system **213** consists of two layers.  The *Raw* layer is
an inductive type with three constructors — two primitive
elements `a`, `b`, and a binary operation
`slash : (x y : Raw) (h : x ≠ y) → Raw` — together with the
distinctness precondition `h : x ≠ y` carried by `slash`.
The four-tuple (a, b, slash, distinctness) — three constructors
plus the precondition — constitutes the *clauses* of the
axiom; the strict-minimality argument of §2.5 treats each as
an independent dimension and shows each to be essential.  The
*Lens* layer specifies homomorphisms out of `Raw` into
arbitrary types, parameterized by a triple
`(base_a, base_b, combine)` with commutative `combine`.

Two design decisions distinguish 213 from set-theoretic
foundations:

(a) `slash` is undefined on equal arguments.  Distinguishing
is therefore *primitive*: equality is not a defined relation
between pre-existing entities, but a precondition for the
combining operation.

(b) The framework commits to no collection axioms (Power-set,
Choice, Infinity).  In their stead, the *Lens* layer specifies
internal observations, and the universal construction
`universalLens` (§5.1) realizes any slash-congruence on `Raw`
as a Lens kernel without external choice.

Section §2.5 proves that each of the four clauses is essential:
removing any one collapses the framework to a trivial structure.
This *strict-minimality* result is internal to the framework
and uses no axiom beyond `propext`.

### §1.2 Position relative to ZFC

213 and ZFC differ in what is taken as axiomatic:

- ZFC posits the existence of certain collections (subsets,
  choice functions, inductive sets) and develops mathematics
  inside them.
- 213 posits only the primitive distinguishing operation, and
  develops corresponding structures as `Lens` specifications
  whose existence is constructed rather than postulated.

§5 exhibits the 213-side counterparts: full reduction of
Choice (§5.1), an explicit boundary witness for Power-set
(§5.2), unbounded-depth `Raw` in place of an Infinity axiom
(§5.3), Comprehension as a distinguishing-closed `Subtype`
under closure precondition (§5.5), and Coproduct via the
`Prism` counterpart (§5.6).  Each is mechanically verified
within the framework, with no appeal to external
set-theoretic arguments.

### §1.3 Verification and contract

Every theorem cited in this paper is verified by the Lean 4
kernel against an explicit axiom budget.  The output of
`#print axioms` for each theorem is bounded by `[propext,
Quot.sound]` (the Lean 4 core baseline).  A full
component-to-axiom map appears in Appendix A.

This bound is taken as a *contract*: see §8 for the
falsifiability statement and its operational consequences.

### §1.4 Related work

Constructive analysis (Bishop, 1967) develops mathematics
around the requirement that every existence claim be
witnessed.  The treatment of Cauchy completeness in §§6-7 is
constructive in the Bishop sense: each cut is given by an
explicit witness `N`, never by an existence claim resting on
LEM.  The framework's *contract* (§8.1) — "an axiom beyond the
baseline triggers theory discard" — is a strict form of the
constructivist commitment.  Bishop's work assumes ℝ as a
Cauchy-completion of ℚ; the present framework constructs cuts
internally as `Lens`-output `Bool` decisions, without ℝ.

Homotopy Type Theory (UFP, 2013) extends Martin-Löf type
theory with the univalence axiom and higher inductive types.
HoTT shares with 213 the type-theoretic standpoint and the
treatment of equality as structure rather than as a pre-given
relation.  The two systems differ in scope: HoTT axiomatizes
identity-type behaviour (univalence) and is intended as a
foundation for synthetic homotopy theory; 213 axiomatizes only
the distinguishing operation and is intended as a substrate
for the algebra of distinctions.  213 uses neither univalence
nor `Quot.mk` beyond the `Quot.sound` baseline.

Lawvere's Elementary Theory of the Category of Sets (ETCS,
1964) replaces ZFC's element-membership axioms with categorical
axioms about the category of sets.  213 follows the same
spirit at the Raw + Lens level: collection axioms (Power-set,
Choice, Infinity) become internal Lens specifications (§5).
Where ETCS axiomatizes a complete topos, 213 axiomatizes only
the initial Raw-algebra and treats further structure as
Lens-derivable.

The Calculus of Inductive Constructions (Coq) and Lean's own
core type theory both support inductive types at the
foundational level.  213 uses Lean 4's inductive `Tree` type
together with a canonical-form `Subtype`.  Mathlib's hierarchy
of algebraic structures (groups, rings, etc.) builds on this
inductive backbone; 213's `HasDistinguishing` typeclass
(§9.1) plays an analogous role at the level of
distinguishability rather than algebraic structure.  No
Mathlib dependency is incurred.

Comparable minimal axiomatizations of mathematics include ZF
without Choice, NF (Quine), Aczel's CZF, and Feferman's
predicative systems.  Each takes set-formation as primitive
and varies the collection axioms.  213 makes the
*distinguishing operation* primitive instead: the basic act
is `slash` on distinct arguments, not `{x : P(x)}`.
Expressive comparison with these systems is open.

### §1.5 Roadmap

§2 introduces the Raw axiom and its Lean implementation.  §3
defines `Lens`.  §4 establishes that the canonical-form total
order is an encoding artifact.  §5 develops the 213-side
counterparts of the ZFC commitment axioms.  §6 develops Cauchy
completeness in the Lens-output setting.  §7 exhibits four
concrete demonstrations: √2 (Pell), the p-adic integers ℤ_p
(mod-tower), e (Euler partial sums), and π/2 (Wallis product).
§8 states the falsifiability contract and the closed
boundaries.  §9 collects the formal results into the *semantic
atom* reading and discusses its scope.  Appendix A maps each
component to its Lean declaration and reported axioms.

---

## §2 The Raw Axiom

### §2.1 The axiom

Two primitive distinct elements `a` and `b`, and a binary
operation `slash` defined on distinct arguments, are postulated.
Equality, order, and any further structure are not postulated;
they are introduced at the Lens layer (§3).  The axiom seed
document `AXIOM.md` records the three-sentence informal
statement; `Firmware/Raw.lean` realizes it as an inductive type.

### §2.2 Tree encoding

The carrier is realized as a free binary tree

```
inductive Tree : Type
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree
```

inside the internal namespace `E213.Firmware.Internal`.  A
canonical-form predicate selects one representative per
directionless equivalence class:

```
def Tree.canonical : Tree → Bool
  | .a            => true
  | .b            => true
  | .slash x y    => x.canonical && y.canonical
                       && (Tree.cmp x y = .lt)
```

The lexicographic comparison `Tree.cmp` orders the children of
a `slash` so that the smaller appears first.  §4 establishes
that the choice of comparison is an encoding artifact: any
`CmpProps`-satisfying total order yields an isomorphic Raw
type.

### §2.3 The Raw subtype

```
def Raw : Type := { t : Tree // t.canonical = true }
```

Smart constructors expose `Raw` as the public API:

```
def Raw.a : Raw := ⟨.a, rfl⟩
def Raw.b : Raw := ⟨.b, rfl⟩
def Raw.slash (x y : Raw) (h : x ≠ y) : Raw
```

The `Raw.slash` constructor canonicalizes its arguments and
returns the canonical-form representative.  The directionless
combination is captured by the theorem `Raw.slash_comm`:

```
theorem Raw.slash_comm (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h = Raw.slash y x h.symm
```

The first few `Raw` levels (`Firmware/RawLevels.lean`) are:

| Level | Raw terms                              | count |
|-------|----------------------------------------|-------|
| 0     | `Raw.a`, `Raw.b`                       |  2    |
| 1     | + `Raw.slash a b _`                    |  3    |
| 2     | + `slash a (slash a b)`, `slash b (slash a b)` | 5 |

Higher levels grow combinatorially.  Each new term is the
`Raw.slash` of two distinct existing terms; canonicalization
ensures one representative per directionless pair.

Equality on `Raw` is decidable: it reduces to equality of the
underlying canonical-form `Tree`, which is decidable as a
finite inductive type.  The `slash` precondition `x ≠ y` is
therefore constructive — a witness can be produced by the
elaborator.

### §2.4 Catamorphism and induction principle

For each algebra `(α, base_a, base_b, combine)` with `combine`
commutative, the catamorphism `Raw.fold` produces a homomorphism
`Raw → α`:

```
def Raw.fold {α : Type} (base_a base_b : α)
    (combine : α → α → α) : Raw → α
```

The `Raw.fold_slash` theorem captures the homomorphism property,
provided `combine` is symmetric:

```
theorem Raw.fold_slash {α} (ba bb : α) (c : α → α → α)
    (hsym : ∀ u v, c u v = c v u) (x y : Raw) (h : x ≠ y) :
    (Raw.slash x y h).fold ba bb c
      = c (x.fold ba bb c) (y.fold ba bb c)
```

`Lens.view_unique` (in `Research/RawInitiality.lean`) shows that
this homomorphism is *unique* under the same hypotheses:

```
theorem Lens.view_unique {α} (L : Lens α)
    (hsym : ∀ u v, L.combine u v = L.combine v u)
    (f : Raw → α)
    (ha : f Raw.a = L.base_a)
    (hb : f Raw.b = L.base_b)
    (hslash : ∀ x y h, f (Raw.slash x y h)
                       = L.combine (f x) (f y)) :
    ∀ r, f r = L.view r
```

Combined existence + uniqueness gives `Lens.initiality`:
in the category of commutative `Raw`-algebras (objects =
triples `(α, base_a, base_b, combine)` with `combine`
commutative; morphisms = algebra-preserving maps), `Raw` is the
*initial object*: there is a unique morphism `Raw → α` to every
object `α`.

A custom eliminator `Raw.rec` allows induction directly on the
`Raw.a / Raw.b / Raw.slash` constructors without exposing the
underlying `Tree` to the user.

### §2.5 Strict minimality of the axiom

`AxiomMinimality.lean` proves that every clause of the Raw axiom
is essential.  Removing any one of them collapses the framework:

| Clause removed | Resulting framework |
|----------------|---------------------|
| `b`            | single element only (`rawA_trivial`) |
| `a`            | single element only (`NoA.rawB_trivial`) |
| `slash`        | static two-element type (`NoSlash.rawAB_only_two`) |
| distinctness   | self-pairing possible — distinguishing collapses (`NoDistinct.self_pairing_exists`) |

All four results are mechanically verified.  The first three
require no axioms; the fourth requires only `propext`.  Hence
the axiom cannot be reduced further without losing the
distinguishing operation.

---

## §3 Lens

### §3.1 Definition

A *Lens* on a type `α` records the data of a `Raw`-algebra:

```
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view {α} (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine
```

When `L.combine` is commutative, `view` is well-defined on
canonical forms (it respects `Raw.slash_comm`) and is the
unique `Raw → α` homomorphism extending `(L.base_a, L.base_b,
L.combine)` (Theorem `Lens.view_unique`, §2.4).

### §3.2 Lens kernel and slash-congruences

Each Lens induces an equivalence relation on `Raw`:

```
def Lens.equiv {α} (L : Lens α) (x y : Raw) : Prop :=
  L.view x = L.view y
```

This kernel is automatically a *slash-congruence*: it is
preserved by the slash operation (`KernelCongruence.lean`):

```
theorem Lens.equiv_slash_congruence (L : Lens α)
    (hsym : ∀ u v, L.combine u v = L.combine v u)
    (x x' y y' : Raw) (hx : x ≠ y) (hx' : x' ≠ y')
    (hxx' : L.equiv x x') (hyy' : L.equiv y y') :
    L.equiv (Raw.slash x y hx) (Raw.slash x' y' hx')
```

Conversely, every slash-congruence arises as the kernel of some
Lens — see §5.1 (`UniversalQuotLens.lean`).

### §3.3 The refines preorder

The relation "L refines M" expresses that L makes finer
distinctions than M:

```
def Lens.refines {α β} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y : Raw, L.equiv x y → M.equiv x y
```

The refines relation is a preorder.  Each Lens has a *canonical
form* under refines-equivalence: by `LensCanonicalForm.lean`,
every `Lens` (with commutative combine) is refines-equivalent
to `universalLens L.equiv`, the `universalLens` built from its
own kernel.  Together with `universalLens_kernel_eq_E` (§5.1)
this identifies the refines-equivalence classes of Lenses with
the slash-congruences on `Raw`.  The two directions are:
`lens_canonical_universal` gives `universalLens (Lens.equiv L)
≈ L` (modulo refines-equivalence); `universalLens_kernel_eq_E`
gives `Lens.equiv (universalLens E) = E` for any
slash-congruence `E`.  The preorder forms a meet-semilattice
(`LensMeet.lean`); its finest element is `idLens`
(distinguishing every Raw) and its coarsest is `constLens`
(making no distinctions).

### §3.4 Examples

Concrete Lenses used in §6–§7:

- `Lens.leaves : Lens Nat`, triple `⟨1, 1, (·+·)⟩` — the leaf
  count.
- `Lens.depth : Lens Nat`, triple `⟨0, 0, λ a b ↦ 1 + max a b⟩`.
- `parityLens : Lens Bool`,  triple `⟨true, true, xor⟩` —
  `view r = true` iff the leaf count of `r` is odd.
- `abLens : Lens (Nat × Nat)` — the pair of `a`- and `b`-counts;
  used in the Cauchy framework of §6 and the demonstrations of
  §7.
- `leavesModNat m : Lens Nat`, the post-composition of
  `Lens.leaves` with `(· % m)`; the family `m ≥ 2` exhibits
  countably many distinct kernels (used in §7.3 for ℤ_p).

`BoolSqClassification.lean` proves that every `Lens Bool` falls
into exactly one of four classes by the value of `combine x x`:
*Collapse-True* (`= true`), *Collapse-False* (`= false`),
*Idempotent* (`= x`), or *NegSq* (`= ¬x`).  For example,
`parityLens` is Collapse-False (`xor x x = false`), and
`negSqLens` (`NegSqLens.lean`) realizes the NegSq class.

Sample views on the level-0 and level-1 `Raw` terms:

|              | `Raw.a` | `Raw.b` | `slash a b` |
|--------------|---------|---------|-------------|
| `Lens.leaves`| 1       | 1       | 2           |
| `Lens.depth` | 0       | 0       | 1           |
| `parityLens` | true    | true    | false       |
| `abLens`     | (1, 0)  | (0, 1)  | (1, 1)      |

---

## §4 Encoding-artifact independence

### §4.1 Statement

The canonical-form predicate of §2.2 fixes one comparison
`Tree.cmp`.  Any other comparison satisfying the same
structural properties yields a Raw type isomorphic to the
original; the choice of comparison has no mathematical content.
This section makes the statement precise.

### §4.2 CmpProps

`Research/CmpIndependence.lean` axiomatizes the structural
content of a comparison:

```
structure CmpProps (cmp : Tree → Tree → Ordering) : Prop where
  eq_iff : ∀ x y, cmp x y = .eq ↔ x = y
  swap   : ∀ x y, cmp x y = (cmp y x).swap
```

These two properties are sufficient to define the canonical
form for any comparison:

```
def canonicalBy (cmp : Tree → Tree → Ordering) : Tree → Bool
def RawBy (cmp : Tree → Tree → Ordering) : Type :=
  { t : Tree // canonicalBy cmp t = true }
```

`Tree.cmp` and its reversal `cmpRev` both satisfy `CmpProps`,
producing two ostensibly different `Raw` types: `Raw` itself
(based on the lexicographic order) and `RawBy cmpRev`.

### §4.3 The transport theorem

A computable Tree-level fold `transportTree` sends each
canonical-form Tree under `cmp1` to its canonical-form
representative under `cmp2`, swapping the children of `slash`
nodes when needed:

```
def transportTree (cmp : Tree → Tree → Ordering) : Tree → Tree
```

The roundtrip theorem establishes that `transportTree cmp2 ∘
transportTree cmp1 = id` on canonical-form trees:

```
theorem transportTree_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) (t : Tree)
    (hcanon : canonicalBy cmp2 t = true) :
    transportTree cmp2 (transportTree cmp1 t) = t
```

Lifting `transportTree` to the subtype level produces a bijection
between `RawBy cmp1` and `RawBy cmp2`:

```
theorem RawBy_bijection (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    ∀ (r : RawBy cmp2),
      transportRawBy cmp1 cmp2 h1 h2
        (transportRawBy cmp2 cmp1 h2 h1 r) = r
```

### §4.4 Example

Take the Raw element `r = a / (a / b)`.  Under `Tree.cmp`, the
canonical encoding orders the children ascendingly:

```
slash a (slash a b)         (cmp = Tree.cmp)
```

Under `cmpRev := λ x y. (Tree.cmp x y).swap`, the same Raw
element receives the canonical encoding

```
slash (slash b a) a         (cmp = cmpRev)
```

with the children of each `slash` node reversed.  The map
`transportTree` swaps children at each node and re-canonicalizes:

```
transportTree cmpRev (slash a (slash a b))
  = slash (slash b a) a
```

Applying `transportTree Tree.cmp` returns the original.  The
roundtrip theorem proves this for all canonical Trees;
`RawBy_bijection` lifts the result to the subtypes.

### §4.5 Remark

`RawBy_bijection` is proved using only `[propext]`.  No
`Classical.choice` is required.  Consequently, the choice of
`Tree.cmp` is an encoding artifact in the sense of `AXIOM.md`
§3 (classification β): no mathematical statement of the
framework depends on it.

---

## §5 ZFC commitments — 213-side counterparts

For each principal ZFC commitment, this section exhibits the
213-side counterpart: full reduction where available, an
explicit boundary witness where the commitment lies outside the
framework's reach.

### §5.1 Choice — full reduction

`Research/UniversalQuotLens.lean` constructs, for any
slash-congruence `E` on `Raw`, a concrete Lens whose kernel is
exactly `E`:

```
def universalLens (E : Raw → Raw → Prop) : Lens (Raw → Prop)

theorem universalLens_kernel_eq_E
    (E : Raw → Raw → Prop)
    (hrefl  : ∀ r, E r r)
    (hsymm  : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r r' : Raw) :
    (universalLens E).view r = (universalLens E).view r' ↔ E r r'
```

The four hypotheses on `E` are the equivalence laws together
with slash-compatibility — i.e., `E` is a slash-congruence.
Conversely, every Lens kernel is a slash-congruence
(`Lens.equiv_slash_congruence`).  Hence the slash-congruences
are exactly the Lens kernels.

`Research/ChoiceResolved.lean` packages this as: any
slash-congruence arises as the kernel of an explicit Lens; no
choice function is needed to select representatives.  The
construction uses only `[propext, Quot.sound]`.

`Research/FamilyMeet.lean` extends the construction to
arbitrary index types: for any family `⟨E_i⟩_{i ∈ I}` of
slash-congruences indexed by an arbitrary type `I` (in
particular `I = Nat` for the countable case), the meet
`familyMeet E := λ r r'. ∀ i, E_i r r'` is itself a
slash-congruence, and `universalLens (familyMeet E)` realises
this meet as a single Lens kernel
(`familyMeet_kernel_eq`).  This subsumes the role of
*countable Choice* in the framework: simultaneous
representative selection across a countable family of
equivalence classes is built from `universalLens` without an
external choice principle.

**Example.**  Define the Lens
`boolXor : Lens Bool := ⟨false, true, xor⟩` and let `E_Xor` be
its kernel:
```
E_Xor r r' := boolXor.view r = boolXor.view r'.
```
`E_Xor` is a slash-congruence (the four hypotheses follow from
equational properties of `=` on `Bool`), and
`universalLens E_Xor` produces a Lens of type
`Lens (Raw → Prop)` whose kernel is exactly `E_Xor`
(`universalLens_kernel_eq_E`).  No representative is selected:
the indicator function `λ r. E_Xor r ·` plays the role of the
Choice-side selector.

### §5.2 Power set — boundary witness

The Lens kernels form a strict subset of the binary relations
on `Raw`.  `Research/NoDepthParity.lean` exhibits an explicit
witness: depth-parity equality on `Raw` is not a slash-congruence
(the full statement is in the module
`NoDepthParity.depthParity_ker_not_slash_cong`), hence not a
Lens kernel.

The function-level analogue, in `Research/DepthParityNotFold.lean`
and packaged in `SemanticAtom.lean`, is

```
theorem exists_non_lens_expressible :
    ∃ f : Raw → Bool, ¬ IsLensExpressible f.
```

The framework therefore does not represent arbitrary subsets
of `Raw`; it represents the fold-structured (slash-congruent)
ones.  The strict-inclusion is established constructively, with
depth parity as a definite witness.

### §5.3 Infinity — unbounded depth

`Raw` is inductively defined and every finite-depth term is
mechanically constructible (`Firmware/RawLevels.lean`).
`Infinity/Countable.lean` and `Infinity/Godel.lean` exhibit an
explicit injection `Nat ↪ Raw`, so `Raw` is countably infinite
without an external Infinity axiom.  `Infinity/Cantor.lean`
further proves a Cantor-style result `cantor_general` for
`Raw → Bool`.

### §5.4 Cardinality of the Lens-kernel space

Beyond the type-theoretic cardinality of `Raw` itself (which is
countable, `Godel.lean`), the framework supports a second
cardinality notion: the size of the space of Lens kernels — the
number of distinct slash-congruences expressible by Lenses on
`Raw`.  This number is at least countably infinite:
`KernelCardinalityLB.lean` exhibits the family
`leavesModNat m`, `m ≥ 2`, giving an injection of `Nat` into
the kernel space.  An uncountable lower bound is open.

### §5.5 Comprehension — distinguishing-closed subtype

For any predicate `P : Raw → Prop` with `P Raw.a` and
`P Raw.b`, `Research/SubtypeInstance.lean` equips the subtype
`{r : Raw // P r}` with a `HasDistinguishing` instance.
A meaningful slash-based combine is supplied in
`Research/SubtypeInstanceClosed.lean` under the additional
`SlashClosed P` hypothesis (a typeclass requiring
`∀ x y h, P x → P y → P (Raw.slash x y h)`).  The closure
hypothesis replaces ZFC's arbitrary-subset commitment with
an explicit slash-closure precondition; the resulting instance
`subtypeHasDistinguishingClosed` uses `[propext]` only.

### §5.6 Coproduct — Prism counterpart

`Research/Prism.lean` introduces `Prism α`, the 213-internal
coproduct counterpart of `Lens` (within the framework: `Lens`
records data for a homomorphism *into* a type, while `Prism`
records data for case-extraction *from* `Raw`).  It carries
operations `preview : Raw → Option α` and `review : α → Raw`.
Concrete instances `aPrism`, `bPrism` and the disjointness
theorem `caseElement_disjoint` formalize the coproduct on the
two primitive elements.

The Sum-type instance `sumHasDistinguishing` of
`Research/SumInstance.lean` uses a priority-based combine
(left-preference on mixed cases).  This is one valid
`HasDistinguishing` instance on `Sum α β`; the priority
combine fails the coproduct universal property in
DistMorphism: with `α = β = γ = Bool` and the xor combine,
`f = g = id` are both algebra morphisms, yet no mediating
morphism `h : Sum Bool Bool → Bool` simultaneously satisfies
`h ∘ inl = id`, `h ∘ inr = id`, and `combine`-preservation
(`SumNotCoproduct.sum_not_coproduct_xor`).  The combine
choice is therefore non-canonical, not merely
under-determined (§8.2).

---

## §6 Cauchy completeness

The framework supports limit constructions internally: a
sequence of `Raw` elements is judged Cauchy with respect to a
Lens (or family thereof), and its limit is captured as
Lens-output data, with no new `Raw` element introduced.  This
is the structure exercised in §7 to exhibit √2, ℤ_p, e, and
π/2 within 213.

### §6.1 Lens-Cauchy and EventuallyClass

A sequence `xs : Nat → Raw` is *Lens-Cauchy* with respect to a
Lens `L` if its tail eventually collapses to a single
`L`-equivalence class:

```
def LensCauchy (L : Lens α) (xs : Nat → Raw) : Prop :=
  ∃ N, ∀ m n, m ≥ N → n ≥ N → L.equiv (xs m) (xs n)

def EventuallyClass (L : Lens α) (xs : Nat → Raw) (c : α) : Prop :=
  ∃ N, ∀ n, n ≥ N → L.view (xs n) = c
```

The two conditions are equivalent
(`cauchy_iff_eventually_class`).  The limit class `c` is
unique (`eventually_class_unique`).

### §6.2 Family-Cauchy and the unified GFCauchy

For families of Lenses, the family-Cauchy condition is the
pointwise version (`FamilyCauchy`).  `Research/GenericFamilyCauchy.lean`
unifies family-Cauchy across structurally different applications
under a single abstract form `GFCauchy L F xs`, parameterized
by a Lens `L : Lens α` and a post-processing family
`F : ι → α → β`.  The abstraction subsumes:

- *Profinite*: `L = Lens.leaves`, `F m = (· % (m+1))`,
  ι = `Nat`, β = `Nat`.  Used for ℤ̂-style profinite limits.
- *Archimedean*: `L = abLens`, `F (m, k) = orderProj m k`,
  ι = `Nat × Nat`, β = `Bool`.  Used for ℝ-Dedekind cuts.

### §6.3 Universal limit Lens

For a family-Cauchy sequence, the limit is captured by an
`OrderCauchyData`-style record (`ArchimedeanCauchy.lean`) that
packages the explicit `N` witnesses for each `(m, k)`:

```
structure OrderCauchyData (xs : Nat → Raw) where
  N : Nat → Nat → Nat
  cauchy : ∀ m k i j, k ≥ 1 → i ≥ N m k → j ≥ N m k →
    orderProj m k (abLens.view (xs i))
      = orderProj m k (abLens.view (xs j))

def OrderCauchyData.cut {xs} (cd : OrderCauchyData xs)
    (m k : Nat) : Bool :=
  orderProj m k (abLens.view (xs (cd.N m k)))
```

The `cut` function is the limit's Dedekind decision: a
`Nat → Nat → Bool` indexed by the rational threshold `m/k`.
At a more abstract level, the equivalence relation
```
E_cd x y := ∀ (m k : Nat),
              orderProj m k (abLens.view x)
                = orderProj m k (abLens.view y)
```
on `Raw` is a slash-congruence and arises as the kernel of a
`universalLens` (§5.1).

The limit is a `Nat → Nat → Bool` decision function on the
rational thresholds; no new `Raw` element is introduced.
Whether the limit cuts at *every* rational threshold depends on
the witness `cd.N`; §7 establishes only the explicit
thresholds, in line with §6.4.

### §6.4 Monotonic-bounded propagation

`Research/MonotonicBoundedCauchy.lean` provides constructive
helpers for *monotonically increasing ab-sequences*.  Defining

```
def IsAbMonotonic (xs : Nat → Raw) : Prop :=
  ∀ n, (abLens.view (xs n)).1 * (abLens.view (xs (n+1))).2
       ≤ (abLens.view (xs (n+1))).1 * (abLens.view (xs n)).2

def IsAbPositiveB (xs : Nat → Raw) : Prop :=
  ∀ n, 1 ≤ (abLens.view (xs n)).2
```

(cross-multiplied monotonicity and positive denominators), the
key propagation theorem is:

```
theorem orderProj_false_propagates (xs : Nat → Raw)
    (hmono : IsAbMonotonic xs) (hpos : IsAbPositiveB xs)
    (m k N : Nat)
    (hN : orderProj m k (abLens.view (xs N)) = false)
    (i : Nat) (hi : i ≥ N) :
    orderProj m k (abLens.view (xs i)) = false
```

Once `orderProj m k` becomes `false` at some `N₀`, it stays
`false` for all `i ≥ N₀`.  A single `false` witness at `(m, k)`
therefore gives the tail-Cauchy property at that threshold,
without LEM.  Both the Euler and Wallis sequences satisfy
`IsAbMonotonic` and `IsAbPositiveB`
(`euler_isAbMonotonic`, `wallis_isAbMonotonic`).

The general statement `∀ (m, k), ∃ N` (the "all cuts" closure)
requires LEM on monotonic Bool sequences and is *deliberately
not claimed*; see §8.2.

`Research/HasModulus.lean` introduces a constructive
modulus typeclass `HasModulus xs` carrying the explicit `N :
Nat → Nat → Nat` as data, in the Bishop-constructive style.
The implication `HasModulus xs → isOrderCauchy xs`
(`isOrderCauchy_of_hasModulus`) is axiom-free.  Sequences
supplied with a `HasModulus` instance therefore close their
all-(m, k) Cauchy property without any LEM appeal; specific
instances for Pell, Euler, Wallis are future work and require
explicit closed-form modulus formulas.

---

## §7 Demonstrations

The Cauchy framework of §6 is exercised on four targets, each
chosen to stress a different facet: an algebraic constant
defined by a quadratic invariant (√2 via Pell), a profinite
sequence under a mod-tower (ℤ_p), a transcendental given by an
infinite series (e via factorial sums), and a transcendental
given by an infinite product (π/2 via Wallis).

### §7.1 Rational diagonal warm-up

`Research/ArchimedeanCauchy.lean` first establishes the warm-up:
for any sequence `xs` with `abLens.view (xs n) = (n+1, n+1)`
(diagonal pair), the sequence is order-Cauchy and its Dedekind
cut is the rational 1.  This validates the abLens + orderProj
framework on a known-rational case.

### §7.2 √2 algebraic — Pell sequence

`Research/PellSeq.lean` constructs the Pell sequence
`(x_n, y_n)` satisfying the invariant `x_n^2 = 2*y_n^2 + 1`,
representing rational approximations to √2.  The recursion
starts from `(3, 2)` and applies `(x, y) ↦ (3x + 4y, 2x + 3y)`:

| n | (x_n, y_n)  | x_n / y_n     |  approximation |
|---|-------------|---------------|----------------|
| 0 | (3, 2)      | 3 / 2         | 1.5            |
| 1 | (17, 12)    | 17 / 12       | 1.4166…        |
| 2 | (99, 70)    | 99 / 70       | 1.4142857…     |
| 3 | (577, 408)  | 577 / 408     | 1.41421568…    |

Each pair is constructively realized as a `Raw` element via
`abLens_witness` (an explicit constructive surjection of `abLens`
on positive `(a, b)` pairs).  Combined with `Sqrt2Cut.lean`'s
key lemmas:

```
theorem pell_orderProj_above (x y m k : Nat)
    (hPell : IsPellSol x y) (hmsq : 2*k*k < m*m)
    (hy_large : k*k ≤ y*y) :
    orderProj m k (x, y) = true

theorem pell_orderProj_below (x y m k : Nat)
    (hPell : IsPellSol x y) (hk : k ≥ 1) (hmsq : m*m < 2*k*k) :
    orderProj m k (x, y) = false
```

The two lemmas cover rational thresholds strictly above and
strictly below √2.  The remaining case `m^2 = 2 k^2` is
vacuous for `k ≥ 1`: this is the irrationality of √2,
formalised within the framework as
`Sqrt2Irrational.sqrt2_irrational` (Lean 4 core, 2-adic
descent).  Hence √2 appears as a Dedekind cut at every
rational threshold via the Pell-sequence approach.

`Research/PellHasModulus.lean` packages this into a
`HasModulus pellRawSeq` instance with the explicit modulus
`N(m, k) := if 2k² < m² then k else 0`, deriving
`pell_isOrderCauchy` (the all-(m, k) Cauchy property)
without LEM.  This is the first concrete instance of the
constructive modulus typeclass §6.4.

### §7.3 ℤ_p number-theoretic — Padic

`Research/Padic.lean` realizes the p-adic integers ℤ_p as a
sub-tower of the leaves-mod-Nat family.  For any base `p ≥ 2`
(when prime, this is precisely ℤ_p; for general `p ≥ 2` the
construction yields a tower decomposable via CRT into ℤ_q for
the prime factors of `p`), the family
`padicFamily p k = leavesModNat (p^(k+1))` indexes the
characteristic mod-p^k projections.  The factorial sequence is
family-Cauchy with respect to this tower, producing the
profinite zero element.  The tower-refinement theorem
`padic_tower_refines` formalizes the canonical projection
ℤ/p^(k+2) ↠ ℤ/p^(k+1).

### §7.4 e transcendental — Euler partial sums

`Research/EulerSeq.lean` defines the partial sums of `e` via the
common-denominator factorial form:

```
def eulerNum : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * eulerNum n + 1

def eulerDen : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * eulerDen n
```

This corresponds to `S_n = ∑_{k=0}^{n} 1/k!`:

| n | eulerNum n | eulerDen n | S_n     | approximation |
|---|------------|------------|---------|---------------|
| 0 | 1          | 1          | 1 / 1   | 1.000…        |
| 1 | 2          | 1          | 2 / 1   | 2.000…        |
| 2 | 5          | 2          | 5 / 2   | 2.500…        |
| 3 | 16         | 6          | 16 / 6  | 2.666…        |
| 4 | 65         | 24         | 65 / 24 | 2.708…        |

Two algebraic invariants are proved by induction:

```
theorem euler_upper_inv : 3 * eulerDen n ≥ eulerNum n + 1
  -- equivalently S_n ≤ 3 - 1/eulerDen n  <  3.

theorem euler_lower_inv (hn : n ≥ 2) :
    eulerNum n ≥ 2 * eulerDen n + 1
  -- equivalently S_n ≥ 2 + 1/eulerDen n  >  2  (for n ≥ 2).
```

These yield two Dedekind cuts at concrete thresholds:
`m/k ≥ 3` ⇒ `orderProj m k = true` for all `n` (always above e);
`m/k ≤ 2` ⇒ `orderProj m k = false` from `n ≥ 2` (always below).
Individual thresholds `m/k ∈ (2, 3)` may in principle be closed
case-by-case via the propagation theorem of §6.4 (a single
false-witness suffices).  What the framework does *not* claim
is the all-thresholds-at-once statement
`∀ (m, k) ∈ (2, 3), ∃ N, ...`, which would require the
LEM-bound closure.

### §7.5 π/2 transcendental — Wallis product

`Research/WallisSeq.lean` defines partial Wallis products with
recursion:

```
wallisNum 0 = 1,   wallisNum (n+1) = wallisNum n * 4 * (n+1)^2
wallisDen 0 = 1,   wallisDen (n+1) = wallisDen n * (2n+1) * (2n+3)
```

Concrete partial products:

| n | wallisNum n | wallisDen n | W_n        | approximation |
|---|-------------|-------------|------------|---------------|
| 0 | 1           | 1           | 1          | 1.000…        |
| 1 | 4           | 3           | 4 / 3      | 1.333…        |
| 2 | 64          | 45          | 64 / 45    | 1.422…        |
| 3 | 2304        | 1575        | 2304 / 1575| 1.463…        |

(target π/2 ≈ 1.5708 — convergence is slow.)

Two algebraic invariants are required:

- **Lower** (W_n ≥ 4/3, for n ≥ 1):
  `3 * wallisNum n ≥ 4 * wallisDen n`.  Inductive step uses the
  polynomial inequality `(2k+1)(2k+3) ≤ 4(k+1)²` (degree 2 in k),
  closed in Lean 4 core by the same expansion-and-`omega` strategy
  as below.
- **Upper** (W_n ≤ 2 − 1/(2n+1)):
  `wallisNum n * (2n+1) ≤ (4n+1) * wallisDen n`.  Inductive step
  uses the polynomial identity
  `(4k+1) · 4(k+1)² + 1 = (4k+5) · (2k+1)²` (degree 3 in k),
  closed via the **Flat-Monomial Strategy**: after expansion,
  generalize `K := k*k` and `M := k*(k*k)` to atoms and
  dispatch with `omega`.  Lean 4 core lacks `ring`, so this
  rewrite-and-omega approach is the substitute.

Together these establish two Dedekind cuts at concrete
thresholds: `m/k ≥ 2` ⇒ `orderProj m k = true` for all n;
`m/k ≤ 1` ⇒ `orderProj m k = false` from n ≥ 1.  Individual
intermediate thresholds in `(1, 2)` may in principle be closed
case-by-case via the propagation theorem of §6.4 (a single
false-witness suffices).  What the framework does *not* claim
is the all-thresholds-at-once statement
`∀ (m, k) ∈ (1, 2), ∃ N, ...`, which would require the
LEM-bound closure.

### §7.6 Scope

Each of the four targets is a sequence of `Raw` elements
observed by `abLens + orderProj` (or `leavesModNat` in the
profinite case).  No external ℝ or ℤ_p is invoked.

For the transcendentals, only the cuts at *explicit* `(m, k)`
thresholds are claimed (e.g., `e ∈ (2, 3)`, `π/2 ∈ (1, 2)`),
not the cut at every rational threshold.  The latter would
require the all-cuts closure of §6.4, which is LEM-equivalent
and not claimed.  Naming the limit "the cut" is therefore an
external convention; the framework supplies the explicit
cuts.

---

## §8 Falsifiability and boundaries

### §8.1 Contract

`AXIOM.md` §5.2.1 states the framework's contract:

> Every result must be derivable from the Raw axiom and the
> Lean 4 core baseline.  Should any result genuinely require
> an additional axiom, the framework is to be discarded — not
> the result alone — since the Raw axiom is claimed as the
> minimum.

Operational consequences:

- External axioms (`Classical.choice`, LEM, `native_decide`,
  etc.) are forbidden in framework derivations.
- Results may be left open temporarily, but a permanent
  obstruction triggers a falsification declaration.
- The Lean kernel is the mechanical auditor.

After the work of §§2-7 and §9, every public theorem reports
`[propext, Quot.sound]` or no axioms (Appendix A).  The
contract is met; the present body of work supplies no
counterexample.

### §8.2 Closed boundaries

Three results have been resolved by establishing the boundary
rather than crossing it:

- **Power-set**: not every binary relation on `Raw` is a
  Lens kernel.  Witness: depth parity
  (`exists_non_lens_expressible`).
- **All-cuts Cauchy closure**: the statement `∀ (m, k), ∃ N`
  on monotonic Bool sequences is LEM-equivalent and is not
  claimed.  Each Cauchy cut is supplied explicitly.
- **Sub-instance combine**: the original
  `SubtypeInstance.lean` carries a degenerate combine; a
  slash-based meaningful combine is supplied in
  `SubtypeInstanceClosed.lean` under `SlashClosed P`
  (§5.5).

The first two reflect the deliberate avoidance of LEM-style
commitments; the third is infrastructural (Lean elaborator).

### §8.3 Open work (incremental)

- Sharper cut bounds for e and π/2 (e.g. `e ≤ 5/2`, `π/2 ≤ 4/3`).
- Further entries in the Lens catalogue.
- Integration of the r5-critique sub-track
  (`213/research/r5-critique/`), which analyses the ℝ-algebra
  assumption underlying an earlier paper draft
  (`papers/paper14_213.tex`); a candidate Paper 2 topic.

### §8.4 Acknowledgments

Mingu Jeong (Independent Researcher) is the originator of the
theory and the source of axiom design.  Claude (Anthropic)
contributed Lean formalization, derivation exploration, and
prose drafting.  Every formal result was verified by the Lean
kernel.

---

## §9 The semantic-atom reading

This section collects the results of §§2-8 into the reading
that 213 plays the role of a *semantic atom* for
distinguishing-based structures.  §9.1 states the formal scope
as (1)-(3).

### §9.1 Formal scope

Define a type `α` to be *distinguishable* if it carries a
`HasDistinguishing α` instance — equivalently, a triple
`(a, b : α, combine : α → α → α)` with `a ≠ b` and `combine`
commutative.  For every such `α`:

1. **Existence.**  There is a homomorphism `universalMorphism :
   Raw → α` (`SemanticAtom.universalMorphism`).
2. **Uniqueness.**  Any other homomorphism agreeing with the
   instance on `a, b, combine` coincides with it
   (`universalMorphism_unique`).
3. **Initiality.**  Bundling (1) and (2): `Raw` is the initial
   object in the category of commutative `Raw`-algebras
   (`raw_initial`; `Lens.initiality`).

The reading "213 is the semantic atom" denotes (1)-(3): in any
distinguishable type, `Raw` is the unique source of
homomorphisms compatible with the instance data.

The instances exhibited in §§5, 7, and Appendix A — the four
`Prop` connectives (Xor, Iff, And, Or), binary products
`α × β`, function spaces `α → β`, the recursive tower
`Lens^n α`, the Sum/Prism counterpart, and Bool, Fin 3, Nat,
Int — each fall under (1)-(3).  No Lean statement quantifies
over "all frameworks"; the formal scope of the reading is
fixed at (1)-(3) on each `HasDistinguishing` instance.

### §9.2 Components

The formal evidence breaks into fifteen components.  Each is
proved in a single Lean module within the axiom budget
`[propext, Quot.sound]`.  The component-to-declaration map is
in Appendix A.

1. **Strict minimum** of the Raw axiom (§2.5).
2. **Distinguishing-framework abstraction**: the
   `HasDistinguishing` typeclass.
3. **Universal property**: `raw_initial`.
4. **Self-application via `Prop`**: each of the four
   connectives Xor, Iff, And, Or yields a `HasDistinguishing
   Prop` instance with an explicit `canonicalMap`.
5. **Function-level boundary**: `exists_non_lens_expressible`.
6. **Lens canonical form**: `lens_canonical_universal`.
7. **Reach catalogue**: instances on Bool, Fin 3, Nat, Int,
   Raw covering the finite/infinite × surjective/non-surjective
   axes.
8. **Categorical structure**: `DistMorphism` (id, comp,
   associativity, neutrality).
9. **Recursive self-application**: `Lens α` is itself an
   instance, so `Lens^n α` exists for every `n`.
10. **Image minimum**: `image_minimum_property`.
11. **Type-constructor closure (product)**: `α × β`.
12. **Type-constructor closure (function)**: `α → β` for
    `[Inhabited α]`.
13. **Cross-instance functoriality**: Bool ↔ Prop morphisms
    commute under `boolToProp` for all four connectives.
14. **Coproduct dual**: `Prism` accessor and a Sum-type
    instance.
15. **Reflection**: every `HasDistinguishing` instance presents
    as a `Lens` whose `view` is its `universalMorphism`.

`SubtypeInstance` (a 213-side counterpart of Comprehension) is
included with a degenerate combine; the meaningful version
awaits the reflection refactor (§8.2).

The components do not assert that *every* type-construction
fits.  They assert that the constructions we tested fit, and
that the cases that resisted (§8.2) failed for identifiable
infrastructural reasons — Lean elaborator boundary, LEM gap —
not for mathematical reasons internal to the framework.

### §9.3 Comparison with ZFC

| Aspect | ZFC | 213 |
|--------|-----|-----|
| Axiom commitments | 9 | 0 (baseline only) |
| Strict minimality formal proof | absent | ✓ `AxiomMinimality` |
| Universal property | absent | ✓ `raw_initial` |
| Boundary explicit | absent | ✓ `exists_non_lens` |
| Self-application | metalanguage split | ✓ Prop + Lens-on-Lens |
| Categorical structure | external | ✓ `DistMorphism` |
| Coproduct universal | encoded via Pair + Union | ✓ `Prism` (dual) |
| Comprehension | axiom | ✓ `Subtype` (with closure) |

The two systems differ in what is taken as primitive: ZFC
postulates the existence of certain collections, 213 postulates
only the distinguishing operation and constructs corresponding
internal structures as Lens specifications.  The comparison is
structural, not evaluative.

### §9.4 Limits

The fifteen components state what holds within the framework.
Four specific limits remain:

- **Raw.fold reduction** is not always unfolded by Lean's
  elaborator on deep nested terms.  The reflection theorem
  `universalAsLens` sidesteps this by re-presenting an
  instance as a `Lens` whose `view` definitionally equals
  `universalMorphism`.
- **Sum-type combine**: the priority-based variant in
  `SumInstance.lean` is one valid instance, but it fails the
  DistMorphism coproduct universal property
  (`SumNotCoproduct.sum_not_coproduct_xor`).  The combine
  choice is non-canonical; canonicity is decided in the
  negative (§5.6).
- **Subtype `combine_sym`** under a slash-based combine: the
  original `SubtypeInstance.lean` uses a degenerate combine;
  the meaningful slash-based version is in
  `SubtypeInstanceClosed.lean` under `SlashClosed P`
  hypothesis (§5.5).
- **All-cuts Cauchy closure** `∀ (m, k), ∃ N` is LEM-equivalent
  on monotonic Bool sequences and is not claimed (§6.4, §8.2).

The first three are infrastructural; the fourth is a deliberate
refusal of LEM.  Each is either sidestepped or scoped, and none
breaks the falsifiability contract.

---

## Appendix A.  Component-to-declaration map

Each row records: the component number from §9.2, a brief
title, the Lean module and representative declaration, and the
output of `#print axioms` for that declaration (either empty
or a subset of `[propext, Quot.sound]`).

| # | Component | Module · Declaration | Axioms |
|---|-----------|----------------------|--------|
| 1 | Strict minimum (no a) | `AxiomMinimality` · `rawA_trivial` | none |
| 1 | Strict minimum (no b) | `AxiomMinimality` · `rawB_trivial` | none |
| 1 | Strict minimum (no slash) | `AxiomMinimality` · `rawAB_only_two`, `rawAB_card_eq_two` | none |
| 1 | Strict minimum (no distinct) | `AxiomMinimality` · `self_pairing_exists` | none |
| 2 | Distinguishing-framework abstraction | `SemanticAtom` · `HasDistinguishing` (typeclass) | none |
| 3 | Universal property (existence) | `SemanticAtom` · `universalMorphism`, `universalMorphism_a/_b/_slash` | propext, Quot.sound |
| 3 | Universal property (uniqueness) | `SemanticAtom` · `universalMorphism_unique` | propext, Quot.sound |
| 3 | Initiality bundled | `SemanticAtom` · `raw_initial` | propext, Quot.sound |
| 4 | Self-application (Xor) | `SemanticAtom` · `propAsDistinguishing`, `canonicalTruthMap_slash` | propext, Quot.sound |
| 4 | Self-application (Iff) | `SemanticAtom` · `propAsDistinguishingIff`, `canonicalIffMap_slash` | propext, Quot.sound |
| 4 | Self-application (And) | `SemanticAtom` · `propAsDistinguishingAnd`, `canonicalAndMap_slash` | propext, Quot.sound |
| 4 | Self-application (Or) | `SemanticAtom` · `propAsDistinguishingOr`, `canonicalOrMap_slash` | propext, Quot.sound |
| 5 | Function-level boundary | `SemanticAtom` · `exists_non_lens_expressible` | propext, Quot.sound |
| 6 | Lens canonical form | `LensCanonicalForm` · `lens_canonical_universal`, `lens_canonical_idempotent` | propext, Quot.sound |
| 7 | Reach (Bool surjective) | `InstanceReach` · `bool_image_surjective` | propext, Quot.sound |
| 7 | Reach (Fin 3 strict) | `InstanceReach` · `fin3_image_in_01`, `fin3_image_strict` | propext, Quot.sound |
| 7 | Reach (Nat surjective) | `InstanceReach` · `nat_image_surjective` | propext, Quot.sound |
| 7 | Reach (Int strict) | `InstanceReach` · `int_image_nonneg`, `int_image_strict` | propext, Quot.sound |
| 7 | Reach (Raw identity) | `InstanceReach` · (Raw self-instance lemmas) | propext, Quot.sound |
| 8 | Categorical identity & associativity | `DistMorphism` · `id`, `comp`, `comp_assoc`, `id_comp`, `comp_id` | propext, Quot.sound |
| 9 | Recursive self-application (Lens Bool) | `LensOnLens` · `lensBoolHasDistinguishing` | propext, Quot.sound |
| 9 | Recursive self-application (generic) | `LensOnLens` · `lensHasDistinguishing` | propext, Quot.sound |
| 9 | Tower n=1..4 | `LensOnLens` · `levelOne`–`levelFour` | propext, Quot.sound |
| 10 | Image minimum closure | `ImageMinimum` · `image_minimum_property` | propext, Quot.sound |
| 11 | Product instance | `PairInstance` · `pairHasDistinguishing`, `universalMorphism_pair_commute` | propext, Quot.sound |
| 11 | Product projections commute | `PairInstance` · `universalMorphism_first/_second` | propext, Quot.sound |
| 12 | Function-space instance | `FunctionSpace` · `funHasDistinguishing` | propext, Quot.sound |
| 12 | Function-space morphism | `FunctionSpace` · `funUniversalMorphism`, `boolFunUniversal` | propext, Quot.sound |
| 13 | Cross-instance (And) | `BoolPropMorphism` · `boolToProp_and`, `universalMorphism_commute` | propext, Quot.sound |
| 13 | Cross-instance (Or) | `BoolPropMorphism` · `boolToProp_or`, `universalMorphism_commute_or` | propext, Quot.sound |
| 13 | Cross-instance (Xor) | `BoolPropMorphism` · `boolToProp_xor`, `universalMorphism_commute_xor` | propext, Quot.sound |
| 13 | Cross-instance (Iff) | `BoolPropMorphism` · `boolToProp_iff`, `universalMorphism_commute_iff` | propext, Quot.sound |
| 14 | Coproduct accessor (Prism) | `Prism` · `aPrism`, `bPrism`, `aPrism_bPrism_disjoint`, `caseElement_disjoint` | propext, Quot.sound |
| 14 | Sum-type instance | `SumInstance` · `sumHasDistinguishing`, `sumCombine_comm` | propext, Quot.sound |
| 14 | Sum-type non-coproduct | `SumNotCoproduct` · `sum_not_coproduct_xor` | propext |
| 15 | Reflection (typeclass→Lens) | `UniversalReflection` · `universalAsLens`, `universalAsLens_view` | propext, Quot.sound |
| §7.2 | √2 irrationality (descent) | `Sqrt2Irrational` · `sqrt2_irrational`, `mul_self_mod_two` | propext, Quot.sound |
| §5.5 | Subtype slash-based combine (closed) | `SubtypeInstanceClosed` · `SlashClosed`, `subtypeHasDistinguishingClosed` | propext |
| §5.1 | Family meet (countable Choice analog) | `FamilyMeet` · `familyMeet`, `familyMeet_kernel_eq` | propext, Quot.sound |
| §6.4 | Constructive modulus typeclass | `HasModulus` · `HasModulus`, `isOrderCauchy_of_hasModulus` | none |
| §7.2 | Pell HasModulus instance | `PellHasModulus` · `pellHasModulus`, `pell_isOrderCauchy` | propext, Quot.sound |

`propext` (propositional extensionality) and `Quot.sound`
(quotient soundness) are part of Lean 4 core's trusted kernel.
No further axiom — no `Classical.choice`, no LEM, no
`native_decide` — appears in any declaration of the
development.

---

## References

The proofs in this paper depend on no external sources beyond
Lean 4 core.  References below are pointers to the development
artifacts (where every theorem mentioned is recorded) and to
the surrounding mathematical and historical context.

### Repository artifacts (primary sources)

- `213/AXIOM.md` — axiom seed document.
- `213/IMPLEMENTATION.md` — Raw + Firmware audit.
- `213/AUDIT_Lean.md` — Lean ↔ axiom correspondence.
- `213/PAPER1_OUTLINE.md` — this paper's structural outline.
- `213/research/infinity-as-lens/notes/` — numbered analysis
  notes 00-99.
- `213/framework/E213/` — Lean 4 formalization (no Mathlib
  dependency).

### Tools

- de Moura, L., Ullrich, S. (2021). *The Lean 4 Theorem Prover
  and Programming Language*. CADE-28.

### Comparable foundations (informational only; not invoked in
proofs)

- ZFC: Zermelo-Fraenkel set theory with Choice.
- Mac Lane, S., Moerdijk, I. (1992). *Sheaves in Geometry and
  Logic*.  Categorical foundations.
- Bishop, E. (1967). *Foundations of Constructive Analysis*.
  Cauchy-real construction.
- Univalent Foundations Program (2013). *Homotopy Type Theory*.
  Type-theoretic foundations with univalence.

### Related framework artifact (separate arc)

- `papers/paper14_213.tex` — earlier abandoned 3-element
  framing.  Superseded by the present paper.

---

*0 sorry, 0 external axioms beyond Lean 4 core baseline.*
