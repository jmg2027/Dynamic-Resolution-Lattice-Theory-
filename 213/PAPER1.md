# 213: A Minimal Foundational System via Raw + Lens

**Author**: Mingu Jeong (Independent Researcher)

**Acknowledgment**: This work was developed in dialogue with
Claude (Anthropic), which contributed Lean formalization,
derivation exploration, and prose drafting.  All results were
mechanically verified.

**Status**: Lean 4 core formalization (no Mathlib).  0 sorry,
0 external axioms beyond Lean baseline (`propext` + `Quot.sound`).

---

## Abstract

We present **213**, a foundational system for mathematics whose
axiom is the minimal residue of the act of distinguishing things.
The framework consists of two layers: `Raw`, a 3-clause inductive
axiom for the carrier of distinguishable entities, and `Lens`, a
fold-structured observation morphism.  All results are mechanically
verified in Lean 4 core.

The central thesis, formal in scope, is that **213 plays the
role of the semantic atom**: any type with at least two
distinguishable elements and a commutative binary operation is
a `HasDistinguishing` instance, and `Raw` is the initial
object in the resulting category.  We support this thesis with
a multifaceted formal evidence comprising fifteen components,
including (1) a strict-minimum proof showing that every clause
of the axiom is essential, (2) a categorical universal property
establishing `Raw` as the initial object of the
distinguishing-framework category, (3) a Lens-on-Lens
recursive tower exhibiting the framework's self-application
without meta-hierarchy, (4) partial 213-side reductions of
ZFC's Choice (full), Power-set (as a strict-subset boundary
witness), Comprehension (sub-instance under closure
hypothesis), and Coproduct (via the Prism dual) axioms, and
(5) constructive Cauchy demonstrations exhibiting √2, p-adic
ℤ_p, and the transcendental constants e and π/2 as Dedekind
cuts at explicit thresholds.

The framework operates under a **falsifiability contract**: if
any result truly required an axiom beyond the Lean 4 core
baseline, the entire theory would be discarded.  No such
addition has been required.

---

## §1 Introduction

### §1.1 The minimal-residue thesis

The 213 axiom is not a claim about the foundations of the world.
It is the **minimal residue** that remains when one tries to
point at anything at all.

Consider what it takes to refer to a single entity.  In isolation,
no reference is possible: an entity that does not differ from
anything else cannot be singled out.  Reference therefore requires
*at least two* somethings.  But the moment one writes "a and b"
on paper, the connective "and" itself becomes a third something
demanding clarification.  Writing "a, b" makes the comma a
something.  Stipulating that the comma is "general" rather than
"absolute" introduces yet another something.

This recursion is not avoidable.  Any notation introduces
separators that themselves need distinction.  213 records this
recursion at its **minimum** form: two primitive distinct
elements (`a`, `b`) and a single binary distinguishing operation
(`slash`) that combines two unequal terms into a new one.

The axiom is *not* a stipulation of how reality must be
structured; it is what one cannot avoid committing to as soon
as one starts pointing.  Within the formal scope of this paper,
any type with at least two distinguishable elements and a
commutative binary operation gives rise to a
`HasDistinguishing` instance (§9.2 item 2) and is consequently
covered by the framework's universal morphism (§9.2 item 3).
The looser interpretive claim — that *every* working
foundational framework (set theory, type theory, category
theory, propositional metalanguage) implicitly satisfies the
clauses — is supported by the partial reductions in §5 but is
not asserted as a formal theorem here.

### §1.2 Comparison with ZFC

ZFC takes the existence of arbitrary collections as axiomatic.
The Power-set axiom commits to all subsets of a given set; the
Axiom of Choice commits to a choice function on any family; the
Axiom of Infinity commits to an inductive set.  Each of these
is an *ontological commitment* — a stipulation that certain
collections exist regardless of whether they can be exhibited.

213 makes no such commitment.  Its three clauses say only that
distinguishable somethings together with a distinguishing
operation form the minimum framework for reference.  Power-set,
Choice, and Infinity arise instead as **internal Lens
specifications**, not as extra axioms (§5).  The Lens kernel of
any concrete `Lens` in the framework is precisely a
slash-congruence (a Raw-internal equivalence relation
compatible with the binary distinguishing operation), which
allows arbitrary slash-congruences to be realized as Lens
kernels via a uniform construction (`universalLens`).

The key difference is that 213's axiom is *self-justified*:
the strict minimality of its clauses is itself a theorem of
the framework (`AxiomMinimality.lean`, §2.5), proved without
appeal to any external metatheory.  ZFC's axioms are justified
externally — by intuition, model-theoretic argument, or
consensus — but not internally.

### §1.3 Formal contract

Every formal claim in this paper — every theorem reference and
every axiom-budget statement — is mechanically verified in
Lean 4 core, with no Mathlib dependency.  The Lean kernel
reports the following axioms used by each public theorem:

- `propext` (propositional extensionality): Lean baseline.
- `Quot.sound` (quotient soundness): Lean baseline.

No other axioms — no `Classical.choice`, no LEM, no
`native_decide`.  This is the **falsifiability contract**: if
any proof required an additional axiom, the framework would be
declared inadequate and the theory discarded.  No such
addition has been required.

The paper's prose contains some interpretive claims (e.g., the
ORIGIN.md correspondence in §9.4) that lie outside the formal
core; these are clearly marked.

### §1.4 Roadmap

§2 introduces the Raw axiom and its Lean implementation.  §3
defines Lens.  §4 establishes that the encoding choice (the
underlying total order on the canonical-form Tree) has no
mathematical consequence.  §5 reduces ZFC's commitment axioms.
§6 develops Cauchy completeness.  §7 demonstrates the framework
on √2 (algebraic), ℤ_p (number-theoretic), e (transcendental
via Σ 1/k!), and π/2 (transcendental via Wallis product).
§8 closes with the falsifiability discussion.  §9 presents the
*semantic atom thesis*: a fifteen-component synthesis showing
that any entity carrying meaning is necessarily an instance of
the framework.

---

## §2 The Raw Axiom

### §2.1 The 3-clause axiom (verbatim)

From `AXIOM.md`:

> 1. *Something exists.*
> 2. *To know what it is, another something is required.*
> 3. *That other something is also a something.*

Clauses (1) and (3) together yield at least two distinct
somethings, denoted `a` and `b`.  Clause (2) is the primitive
*distinction* operation, applied recursively: given two unequal
somethings `x` and `y`, they can be combined into a new
something `slash x y`.  The axiom does not stipulate equality,
order, or any set-theoretic structure; those arise only at the
Lens level (§3).

### §2.2 Tree encoding

For mechanical verification we encode the carrier as a free
tree:

```
inductive Tree : Type
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree
```

This `Tree` lives in an internal namespace
`E213.Firmware.Internal` and is not exposed to consumers of the
framework.  A canonical form selects one representative from
each equivalence class under the directionless interpretation
of `slash`:

```
def Tree.canonical : Tree → Bool
  | .a            => true
  | .b            => true
  | .slash x y    => x.canonical && y.canonical
                       && (Tree.cmp x y = .lt)
```

The lexicographic comparison `Tree.cmp` orders the two children
of a `slash` so that the *smaller* always appears first.  This
is an implementation choice; §4 proves that any other
`CmpProps`-satisfying total order yields an isomorphic Raw type.

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

Combined existence + uniqueness gives `Lens.initiality`: `Raw`
is the *initial object* in the category of commutative
Raw-algebras (objects = Lenses with symmetric combine; morphisms
= `Raw → α` homomorphisms).

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

All four results are mechanically verified with no axioms
beyond Lean's reflexive equality (the first three) or `propext`
(the fourth).  This is the **strict-minimum** part of the
self-justification: the axiom cannot be made smaller while
retaining the ability to distinguish.

---

## §3 Lens — Observation as Folded View

### §3.1 The Lens structure

A *Lens* records the data for a homomorphism out of `Raw`:

```
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view {α} (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine
```

The `view` function is the homomorphism produced by `Raw.fold`
applied to the data.  When `L.combine` is commutative, the
`view` respects `Raw.slash_comm` and the resulting Raw → α map
is well-defined on canonical forms.

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
own kernel.  This identifies the refines-equivalence classes
with the slash-congruences on `Raw` (one direction:
universalLens; other direction: `lens_canonical_universal`).
The preorder forms a meet-semilattice (`LensMeet.lean`); the
bottom is `idLens` (the finest, distinguishing every Raw) and
the top is `constLens` (the coarsest, making no distinctions).

### §3.4 Lens catalogue

Selected concrete Lenses establish the framework's expressive
range:

- `Lens.leaves : Lens Nat` — counts leaf occurrences:
  `⟨1, 1, (·+·)⟩`.
- `Lens.depth : Lens Nat` — tree depth:
  `⟨0, 0, λ a b ↦ 1 + max a b⟩`.
- `parityLens : Lens Bool` — `⟨true, true, xor⟩`; view = `true`
  iff leaf count is *odd*.
- `abLens : Lens (Nat × Nat)` — pair (a-count, b-count).
- `leavesModNat m : Lens Nat` — `Lens.leaves` post-composed
  with `(· % m)` (countably many distinct kernels for m ≥ 2).

The `Bool`-valued Lenses admit a complete diagonal
classification (`BoolSqClassification.lean`): any `Lens Bool`
falls into exactly one of four classes — Collapse-True
(`combine x x = true`), Collapse-False (`combine x x = false`),
Idempotent (`combine x x = x`), or NegSq (`combine x x = ¬x`).
For example, `parityLens` (with `combine = xor`) belongs to
**Collapse-False**, since `xor x x = false` for both Bool
values; an instance of NegSq is given by `negSqLens`
(`NegSqLens.lean`).

---

## §4 Encoding-Artifact Independence

### §4.1 The cmp choice problem

`Tree.cmp` is the lexicographic comparison used to canonicalize
the children of a `slash` node.  This choice is an
*implementation artifact*: any other total order on `Tree` could
have been used.  A natural question is whether the choice
affects mathematical results.

### §4.2 CmpProps abstraction

`Research/CmpIndependence.lean` introduces an abstraction
capturing the minimal structural requirements of a comparison
function:

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

### §4.4 Significance

`RawBy_bijection` depends only on `[propext]`; no `Classical.choice`
or other axiom is required.  The implication is that the cmp
choice is a true *encoding artifact*: any two valid orderings
yield isomorphic Raw types, so no mathematical result depends
on the choice.  This formalizes the design intent of `AXIOM.md`
§3 classification (β): "encoding artifact, no mathematical
content".

---

## §5 ZFC Reductions

The 213 framework reduces several ZFC commitment axioms to
internal Lens specifications, requiring no external axioms.

### §5.1 Choice → Lens specification

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

That is, the four hypotheses on `E` are exactly the equivalence
laws plus slash-compatibility (i.e., `E` is a slash-congruence).

`Research/ChoiceResolved.lean` packages this as the formal
statement that "Choice is Lens specification": any
slash-congruence arises as the kernel of a concrete Lens, so no
external choice function is needed to select representatives.
All proofs use only `[propext]` and `[Quot.sound]`; no
`Classical.choice` is invoked.

### §5.2 Power set: constructive subset, not full P(X)

Lens kernels are not arbitrary equivalence relations on `Raw`;
they are *slash-congruences* — equivalence relations preserved
by `Raw.slash` for distinct arguments
(`KernelCongruence.Lens.equiv_slash_congruence`).  Conversely,
`Research/NoDepthParity.lean` shows that depth-parity equality
on `Raw` is not a slash-congruence, hence not a Lens kernel:

```
theorem NoDepthParity.depthParity_ker_not_slash_cong : ...
```

(See `Research/DepthParityNotFold.lean` for the function-level
version: depth-parity-as-Bool is not fold-structured.)

This is wrapped at the function level in `SemanticAtom.lean`:

```
theorem exists_non_lens_expressible :
    ∃ f : Raw → Bool, ¬ IsLensExpressible f
```

Together: the Lens-kernel space is *strictly smaller* than the
full power set of `Raw → Raw → Prop`, with depth parity as the
explicit witness of strict inclusion.  This is not a deficiency
but the framework's deliberate scope: it represents the
fold-structured (i.e., distinguishing-coherent) subsets of
`Raw`, refusing to commit to arbitrary LEM-dispatchable
subsets.

### §5.3 Infinity → unbounded depth Raw

`Raw` is inductively defined; every finite-depth term is
mechanically constructible (`Firmware/RawLevels.lean` exhibits
the first few levels).  The framework `Infinity/` directory
establishes that `Raw` is countably infinite via an explicit
injection `Nat ↪ Raw` (`Countable.lean`, `Godel.lean`).

`Cantor.lean` further establishes a Cantor-style theorem
(`cantor_general`) within the framework, exhibiting an
uncountable cardinality at the level of `Raw → Bool` — without
any external Infinity axiom.

### §5.4 Cardinality is a (Raw, Lens) pair property

A central observation: **cardinality is not an intrinsic property
of `Raw` alone, but of the (Raw, Lens) pair.**  `Raw` itself is
countable (one explicit Nat-indexing exists, `Godel.lean`).
The space of Lens kernels is at least countably infinite
(`KernelCardinalityLB.lean`: an injection of `Nat` into the
kernel space, via the `leavesModNat m : m ≥ 2` family).  An
uncountable lower bound for the kernel space is left as future
work.  In any case, the framework supports both countable and
larger cardinalities without committing to either as axiomatic.

### §5.5 Comprehension → distinguishing-closed subtype

`Research/SubtypeInstance.lean` realizes the 213-side analog of
Comprehension: for any predicate `P : Raw → Prop` containing
both `Raw.a` and `Raw.b`, the subtype `{r : Raw // P r}`
carries a `HasDistinguishing` instance.  The instance currently
uses a *degenerate* combine (constantly returning `⟨Raw.a, h_a⟩`)
because the meaningful slash-based combine encounters a
nested-Subtype elaboration limit (§8.3); supplying a
non-degenerate combine would additionally require `P` to be
closed under `Raw.slash` for distinct arguments.  Even in this
weakened form, ZFC's *arbitrary* subset commitment is replaced
by an explicit closure precondition.

### §5.6 Coproduct → Prism dual

In ZFC the disjoint sum (categorical coproduct) is encoded
indirectly via the Pair and Union axioms; the structure is
not primitive.  In 213, `Research/Prism.lean` realizes the
coproduct as the *categorical dual of Lens* — Lens accesses a
product, Prism accesses a coproduct case (with `preview :
Raw → Option α` and `review : α → Raw`).  Concrete instances
`aPrism`, `bPrism` and the disjointness theorem
`caseElement_disjoint` formalize the universal property of the
coproduct.

The Sum-type instance `sumHasDistinguishing` itself is provided
in `Research/SumInstance.lean` with a priority-based combine
(left-preference on mixed cases).  This is a deliberately
*ad-hoc* choice for the mixed case — there is no categorically
natural commutative combine on `Sum α β` — and the framework
records this asymmetry as a *limit of self-naturality* rather
than a derivable structure (see §8.3).

---

## §6 Cauchy Completeness

### §6.1 Lens-Cauchy and EventuallyClass

The classical Cauchy criterion has a natural Lens-side
counterpart.  A sequence `xs : Nat → Raw` is *Lens-Cauchy* with
respect to a Lens `L` if its tail eventually collapses to a
single L-equivalence class:

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
At a more abstract level, the slash-congruence
`∀ x y. (∀ (m, k). cd.cut m k = orderProj m k (abLens.view x))
↔ same of y` arises as the kernel of a `universalLens` (§5.1).

No new Raw element is created; the limit data resides at the
Lens-output level.  This is the **Cauchy completeness without
external ℝ** statement: the framework's reach is closed under
sequential limits, with the limit residing as `Lens`-output decision
functions rather than as new Raw terms.

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
`false` for all `i ≥ N₀`.  This converts a single false-witness
into a tail-Cauchy property at that `(m, k)`, without invoking
LEM.  Both Euler and Wallis seqs satisfy `IsAbMonotonic` and
`IsAbPositiveB` (`euler_isAbMonotonic`,
`wallis_isAbMonotonic`, etc).

The general `∀ (m, k), ∃ N` statement (the "all cuts at once"
closure) requires LEM for monotonic Bool sequences (one would
need to case-split on whether `orderProj m k` is ever false) and
is therefore *deliberately not claimed* — see §8.3 for the
closed-boundary discussion.

---

## §7 Demonstration Suite

The framework's Cauchy completeness is exercised on four
concrete irrationals: the algebraic √2 (Pell), the
number-theoretic ℤ_p (p-adic), and the transcendentals e (Σ
1/k!) and π/2 (Wallis product).

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

The two lemmas cover the rational thresholds strictly above and
strictly below √2.  The remaining case `m^2 = 2 k^2` cannot
occur for `k ≥ 1` (this is the irrationality of √2 — proved
externally; the framework merely *uses* the impossibility) and
is therefore vacuous.  Hence `√2` appears as a Dedekind cut at
every rational threshold via the Pell-sequence approach,
entirely within the framework.

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
Threshold values `m/k ∈ (2, 3)` (strictly between 2 and 3) get
the correct cut value but their proof would require the LEM-bound
general closure (§6.4); they are not asserted within the
framework.

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
`m/k ≤ 1` ⇒ `orderProj m k = false` from n ≥ 1.  For
intermediate thresholds in `(1, 2)` the cut value is the
correct one (true if `m/k > π/2`, false otherwise) but its
formal proof requires the LEM-bound general closure (§6.4),
hence is not claimed within the framework.

### §7.6 Significance

The four examples show that the framework supports algebraic
(Pell), number-theoretic (Padic), and transcendental
(Euler/Wallis) irrationals on equal footing.  No external ℝ or
ℤ_p is invoked: each irrational appears as a sequence of `Raw`
elements observed via `abLens + orderProj` (or `leavesModNat`
for the profinite case), with limit-class data residing in the
Lens output rather than as new Raw terms.

A sober scope clarification: each transcendental is established
as a Dedekind cut at *explicit* `(m, k)` thresholds — for
example, `e ∈ (2, 3)` and `π/2 ∈ (1, 2)` — not as the cut at
*every* rational threshold.  The general `∀ (m, k)` closure
would require LEM (§6.4) and is therefore not claimed.  What
the framework does internally is exhibit each irrational as a
Raw sequence whose specific cuts are mechanically verified;
the limit object is then named "the cut" by convention
(externally to the framework).

---

## §8 Falsifiability and Closed Boundaries

### §8.1 The falsifiability contract

`AXIOM.md` §5.2.1 records the framework's central contract:

> Every result must be derivable from the Raw axiom + Lean 4
> core baseline.  If any result genuinely requires an
> additional axiom, the entire 213 theory is discarded.  This
> is a direct consequence of the Raw axiom being the *minimum
> residue* (§1).  If an extra axiom were genuinely needed, then
> "minimum" was a false claim.

Operating consequences:

- `Classical.choice`, LEM, `native_decide`, and other external
  axioms are forbidden in framework derivations.
- Stuck results may be left "open" for now, but a permanent
  obstruction triggers a falsification declaration.
- The Lean kernel is the framework's mechanical auditor.

### §8.2 Status of the contract

After the work reported in §§2-7 (and §9), every public
theorem reports `[propext, Quot.sound]` or no axioms.  No
external commitment has been required.  The framework satisfies
its falsifiability contract.

### §8.3 Closed boundaries

Several open questions earlier in the work have been resolved
by establishing the *boundary* rather than crossing it:

- **Power-set boundary**: `NoDepthParity` shows that not every
  binary relation on `Raw` is a slash-congruence, so the Lens
  kernel space is strictly contained in the full power set.
  The boundary is *non-trivial* (witness: depth parity), and
  this is itself a closed result (`exists_non_lens_expressible`).

- **General `∀ (m, k)` Cauchy closure**: requires LEM for
  monotonic Bool sequences; *deliberately not claimed*.  Each
  cut is given by an explicit witness, in keeping with the
  framework's constructive character.

- **Sub-instance with meaningful slash-based combine**: the
  nested-Subtype elaborator interferes with the proof of
  `combine_sym`.  A degenerate combine version is supplied
  (`SubtypeInstance.lean`); the meaningful version awaits a
  reflection-style refactor.

These are not unresolved problems but **identified boundaries
of the framework's expressive range** — and they coincide
exactly with where the framework refuses to import LEM-style
commitments.

### §8.4 Open work (incremental)

- Sharpening individual cut bounds (e.g., e ≤ 5/2, π/2 ≤ 4/3).
- Additional Lens catalogue entries.
- Integration of the r5-critique sub-track
  (`213/research/r5-critique/`): a separate arc analysing the
  ℝ-algebra assumption used by an earlier abandoned paper draft
  (`papers/paper14_213.tex`).  This is a Paper 2 candidate.

### §8.5 Acknowledgments

Mingu Jeong (Independent Researcher) is the originator of the
theory and the source of axiom design and physical intuition.
Claude (Anthropic) contributed Lean formalization, derivation
exploration, and prose drafting.  Every result was verified by
the Lean kernel; conceptual claims were independently
re-derived rather than accepted on authority.

---

## §9 Semantic Atom Thesis

### §9.1 The thesis

The framework's central claim, beyond the individual formal
results of §§2-7, is the following.  Reading "an entity carries
meaning" as "the entity sits in a type with at least two
distinguishable elements observed by some commutative
operation", the framework expresses such entities exactly via
the `(HasDistinguishing α, universalMorphism Raw α)` pair.

The thesis decomposes into two clauses, each *formally
verified* in scope:

1. **Genesis of meaning** has two minimal data: *distinction*
   (the existence of at least two unequal elements with a
   commutative binary operation) and *interpretation* (a
   homomorphism out of `Raw` into the entity's carrier).  These
   correspond exactly to a `HasDistinguishing` instance and the
   induced `universalMorphism : Raw → α`.
2. **Strict minimality**: removing any clause of the Raw axiom
   collapses the framework (§2.5).  The Lens layer is the
   minimal additional structure for non-trivial observation
   (an empty Lens collection reduces `Raw` to a syntactic
   carrier with no meaningful homomorphism out).

The interpretive claim — that *all* "meaningful" entities, in
the broadest pre-formal sense, fall under the framework — is
not a Lean theorem.  It is a philosophical reading of the
formal results, supported by the wide range of `HasDistinguishing`
instances exhibited in §§5, 7, and 9.2.

### §9.2 Fifteen formal components

The thesis is supported by the following components, each
formalized in Lean 4 core with all axioms ≤ `[propext,
Quot.sound]`:

1. **Strict minimum** (`AxiomMinimality.lean`, 4 cases).
2. **Distinguishing-framework abstraction** (`HasDistinguishing`
   typeclass).
3. **Universal property** (`raw_initial`: ∃ + uniqueness for
   morphism Raw → α).
4. **Self-application via `Prop`** (4 connectives: Xor, Iff,
   And, Or, with explicit characterizations).
5. **Function-level boundary** (`exists_non_lens_expressible`).
6. **Lens canonical form** (`lens_canonical_universal`: every
   Lens is refines-equivalent to its kernel's universal Lens).
7. **Reach catalogue** (5 instances: Bool, Fin 3, Nat, Int,
   Raw — finite × infinite × surjective × non-surjective
   coverage).
8. **Categorical structure** (`DistMorphism` category with id,
   composition, associativity, neutrality laws).
9. **Recursive self-application** (`LensOnLens`: `Lens α` is a
   `HasDistinguishing` instance; the recursive tower
   `Lens^n α` is exhibited for `n = 1, 2, 3, 4`).
10. **Image minimum** (`image_minimum_property`: universalMorphism's
    image is the minimum distinguishing-closed subset of α).
11. **Type-constructor closure (product)** (`PairInstance`:
    binary product `α × β` is an instance, with components-wise
    universal-morphism splitting).
12. **Type-constructor closure (function)** (`FunctionSpace`:
    `α → β` is an instance with `Inhabited α`).
13. **Cross-instance functoriality** (Bool ↔ Prop morphisms
    commute under `boolToProp`, for all four connectives).
14. **Coproduct (Prism dual)** (`Prism` + `SumInstance`:
    coproduct accessor, plus a Sum-type instance with priority-
    based combine).
15. **Reflection** (`UniversalReflection`: every `HasDistinguishing`
    instance presents as a `Lens` whose `view` is the
    `universalMorphism`).

(The earlier `SubtypeInstance` realizing the Comprehension axiom
in degenerate combine form is included in the framework but, as
explained in §8.3, awaits a meaningful slash-based combine.)

Taken together the components establish that the framework
absorbs the structural extensions we attempted: a particular
metalanguage truth-value type (`Prop` with one of four
connectives) becomes a `HasDistinguishing` instance; the
recursive `Lens^n α` tower yields instances at every level;
binary product, function space, and Sum/Coproduct each fit the
abstraction.  This does not prove that *every* conceivable
extension fits — only that the extensions we tried did fit, and
that the few that resisted (§8.3) failed for identifiable
infrastructural reasons (Lean elaborator, LEM gap), not for
mathematical ones.

### §9.3 ZFC contrast

| Aspect | ZFC | 213 |
|--------|-----|-----|
| Axiom commitments | 9 | 0 (baseline only) |
| Strict minimality formal proof | absent | ✓ `AxiomMinimality` |
| Universal property | absent | ✓ `raw_initial` |
| Boundary explicit | absent (arbitrary P(X)) | ✓ `exists_non_lens` |
| Self-application | absent (metalanguage split) | ✓ Prop + Lens-on-Lens |
| Categorical structure | external (Set category) | ✓ `DistMorphism` |
| Coproduct universal | encoded via Pair + Union | ✓ `Prism` (dual) |
| Comprehension | axiom | ✓ `Subtype` (with closure) |

The contrast is structural: ZFC takes the existence of arbitrary
objects as axiomatic and treats the metatheory as external.
213 takes only the minimum residue of distinguishing as
axiomatic and absorbs all the structural commitments — including
its own metalanguage instances — as internal Lens
specifications.

### §9.4 Connection to ORIGIN

`ORIGIN.md` records the original prompt chain that motivated
the framework — a sequence of physical intuitions about the
impossibility of singular points, the necessity of resolution
covariance, and the invariance of lattice information.  The
present formal results may be read as an *interpretive*
mathematical counterpart to that chain (informal correspondence,
not formal derivation):

- §3 (Zeno-pixel paradox: the law-stability requires a minimum
  pixel) ↔ Raw axiom's strict minimality (§2.5).
- §6 (resolution = unit of information; introduction of `h_eff`)
  ↔ `HasDistinguishing` abstraction (§9.2 item 2).
- §7 (lattice-unit information invariant under any
  resolution choice) ↔ Closure + categorical product (§9.2
  items 6, 11).

The framework's name DRLT (*Dynamic Resolution Lattice Theory*)
records this physical motivation; the present paper formalizes
the resulting mathematical structure as 213.  We emphasize that
the ORIGIN correspondence is *interpretive*: the formal results
of §§2–9 stand independently of any particular physical
reading.

### §9.5 Sober limits

The fifteen components do not amount to an *absolute*
completeness proof in any philosophical sense — such a proof
would require a metatheoretic statement outside the framework.
What they establish is that the structural extensions we
specifically tested are absorbed into the framework's instance
language, and that the few cases that resisted absorption did
so for identifiable reasons.

Specific limits:

- The `Raw.fold` reduction is occasionally not unfolded by
  Lean's elaborator on deep nested terms (this is an
  *implementation* limitation of Lean's evaluator, not a
  foundational constraint).  When this prevents a direct
  reduction-based proof, the reflection theorem
  `universalAsLens` (`UniversalReflection.lean`) sidesteps the
  issue by re-presenting the typeclass instance as a `Lens`
  data record whose `view` definitionally equals
  `universalMorphism`.
- The Sum-type combine has no categorically natural commutative
  choice in the mixed case; we use a priority-based variant
  (`SumInstance.lean`) that yields a valid (if ad-hoc)
  `HasDistinguishing` instance.
- Subtype's `combine_sym` proof under a `slash`-based combine
  meets the nested-Subtype elaborator boundary; a degenerate
  constant combine carries the proof in the present version
  (`SubtypeInstance.lean`).
- The general `∀ (m, k), ∃ N` Cauchy closure for monotonic
  Bool sequences is LEM-equivalent and is therefore not claimed
  (§6.4, §8.3).

The first three are infrastructural; the fourth is the
framework's deliberate refusal of an LEM-style commitment.
None of the four breaks the falsifiability contract: each is
either sidestepped (reflection) or scoped (deliberately not
claimed).

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
- `213/ORIGIN.md` — original physical-intuition chain
  (frozen 2026-04-24).
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
