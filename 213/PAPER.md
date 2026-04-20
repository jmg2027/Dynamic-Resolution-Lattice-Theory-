# The Minimal System of Binary Relations

**Axiom.**

1. *Something exists.*
2. *To know what it is, another something is required.*
3. *That other something is also a something.*

Clauses (1)+(3) give at least two somethings; clause (2) is the
primitive *distinction*, applied recursively. We take these three
clauses as the sole axiom and derive the resulting structure.

Semantic reading of "another" (2) and "between" (2–3):

- **Anti-reflexive:** `slash x x` is not a valid term; distinguishing
  `x` from `x` conveys nothing.
- **Symmetric:** `slash x y = slash y x`; "between" is directionless.

## 0. The logical order of the derivation

The axiom supplies a single type — `Raw`, the free commutative
magma on two generators with no fixed points. **It supplies
nothing else.** No numbers, no sizes, no equality, no order — not
even a way to say that two Raw terms are "different". Those
notions belong to *measurement*, and measurement requires a
**Lens**.

A Lens is a measurement apparatus: a codomain `α` plus two base
values and a binary combine, producing a fold `Raw → α`. Distinct
Lenses yield distinct measurements of the same Raw.

The question we settle below is:

> *For an object within the space `Raw` to recognise itself — to
> distinguish itself from the other Raw terms it is surrounded
> by — which Lens must it use?*

The answer is determined not by the axiom, but by the
**structure of the space `Raw` itself**. The axiom produces
Raw; Raw has structural facts; an observer internal to Raw
requires a Lens that respects those facts. Five structural
constraints arise:

- **(R1)** binary combine (Raw has the `slash` constructor);
- **(R2)** recursive faithfulness (Raw is freely inductive —
  the Lens must be a catamorphism);
- **(R3)** non-vanishing (presence of Raw terms is preserved —
  the combine has no zero divisors);
- **(R4)** swap matches exactly one nontrivial involution on
  the codomain (Raw carries `Aut(Raw) ≅ ℤ/2` as a structural
  invariant);
- **(R5)** minimal continuous distinguishing codomain — all
  Raw terms project to distinct values of a connected ℝ-algebra.

None of these is postulated; each is read off Raw as a space
(§§1–2). The axiom creates the space; the space's internal
geometry enforces the Lens conditions.

R1+R2+R3+R5 fix the codomain's base ring: the minimal
continuous no-zero-divisor ℝ-algebra is **`ℝ`**. R4 then adjoins
the unique nontrivial involution: the minimal extension of `ℝ`
carrying one involution is **`ℂ = ℝ[i]`**, with the involution
realised as complex conjugation. Thus `ℂ` is the unique
self-recognising codomain (§4).

Only with `ℂ` in hand does "size / count / dimension" become a
meaningful notion of Raw; §5 then records the atom set
`{2, 3}`, the unique atomic vertex count `n = 5`, and the
canonical `(3, 2)` partition as *consequences visible under the
`ℂ` lens* — **not** as primitive data of the axiom.

The paper is organised in this order. It contains no
stipulations: every numerical fact below depends on the `ℂ`
lens, and the `ℂ` lens is forced from the axiom alone.

---

## 0'. Notation and conventions

- `Fin n` denotes the standard `n`-element type `{0, …, n-1}`.
- `inductive T` denotes an initial algebra presentation: `T` is
  the smallest type closed under the listed constructors.
- All claims below are formally checked in Lean 4
  (`E213.*` modules, 0 `sorry`); we cite the Lean name where
  relevant, marking "partial" or "prose only" when coverage is
  incomplete.
- The axiom supplies no equality or inequality primitive on
  `Raw`. Lean's propositional equality is external bookkeeping;
  apartness becomes meaningful only through a Lens.

---

## 1. Firmware: the Raw type

### 1.1 Target structure

The axiom's three clauses name two initial somethings `a, b`, a
binary *distinction* operator `slash` that takes two (necessarily
distinct, by (2)) somethings to a new something, and recursion
(clause (3): the output is again a something, so `slash` applies
to it in turn).

**Definition 1.1 (Raw, target).** The target firmware is the
**free commutative magma on two generators with no fixed points**
— the unique closure of `{a, b}` under a symmetric, anti-reflexive
binary operation `slash`.

Raw contains no natural number, no notion of size, no equality
relation beyond "same Lean constructor application". The axiom
introduces no such data.

### 1.2 Lean encoding

Lean 4 core has no primitive quotient types on arbitrary
relations, and we import no set theory (no `Multiset`, no
Mathlib). We encode the target (Def 1.1) as a canonical-form
subtype of a free ordered magma. An auxiliary total order on
trees picks a unique representative per unordered pair; *the
ordering is the encoding's selection function, not a property of
the axiom*. This is the minimal Lean 4 native realisation of the
intended quotient — no external logical apparatus.

```
-- Internal (private): the free ordered magma.
inductive Tree
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree

-- Structural lex compare. Serves only to pick canonical reps.
def Tree.cmp : Tree → Tree → Ordering

-- Canonical: every slash node has strictly ordered children.
def Tree.canonical : Tree → Bool

-- Raw: the canonical subtype.
def Raw : Type := { t : Tree // t.canonical = true }
```

The smart constructor `Raw.slash : (x y : Raw) → x ≠ y → Raw`
canonicalises child order; `Raw.slash_comm` certifies both
input orderings collapse to the same Raw term — the axiom's
symmetric reading at the type level. (Lean:
`E213.Firmware.Raw.slash`, `E213.Firmware.Raw.slash_comm`.)

### 1.3 Recursive bootstrapping

The axiom supplies no "size" concept, but it does supply a
recursive generation rule. Starting from `{a, b}`, each
application of `slash` on two distinct existing terms produces a
new term, and that new term can itself enter further `slash`
applications. The *closure of Raw under `slash`* is therefore an
ever-expanding family; to speak of any specific Raw term is to
identify a particular finite bootstrapping path.

This is all the structure Raw provides. Everything else — "how
many terms at depth 2", "what is the leaves count", "which terms
are 'the same size'" — belongs to measurement, which begins in
§3 with the Lens framework and is pinned down uniquely in §4.

---

## 2. Symmetry of `Raw`

Before any measurement enters, Raw already carries one structural
fact: the two base tokens `a, b` play symmetric roles. The axiom
introduces no asymmetry between them, so exchanging them extends
to a bijection of Raw that respects the `slash` constructor. This
is `Raw`'s only structural content prior to the Lens.

**Definition 2.1 (Swap).**

```
  swap a           := b
  swap b           := a
  swap (slash x y) := slash (swap x) (swap y).
```

At the canonical-form level (§1.2), swapping children of a
`slash` node may violate the ordering; Lean re-canonicalises
after each swap. The re-canonicalisation is an implementation
detail of §1.2's encoding. (Lean: `E213.Firmware.Raw.swap`.)

**Theorem 2.2 (Involution).** `swap (swap x) = x` for all `x`.

*Proof.* Induction on `x`. Base: direct. Step:
`swap (swap (x/y)) = swap (slash (swap x) (swap y)) = slash x y`
by IH. ∎ (Lean: `E213.Firmware.Raw.swap_swap`.)

**Corollary 2.3 (Bijectivity).** `swap` is a bijection of Raw.
(Lean: `swap_injective, swap_surjective, swap_bijective`.)

**Definition 2.4 (Raw-automorphism).** A bijection `φ : Raw → Raw`
with `φ(slash x y h) = slash(φx)(φy)h'` and
`(φa, φb) ∈ {(a, b), (b, a)}`. Such `φ` is fixed by its action on
the base tokens.

**Theorem 2.5 (Automorphism structure).** `swap` is the unique
nontrivial Raw-automorphism; together with the identity, the set
`{id, swap}` forms a two-element group under composition.

*Proof.* By Def 2.4 an automorphism is determined by a base
permutation; there are exactly two. Involutivity (Thm 2.2) and
`swap ≠ id` ensure the two elements are distinct. Composition
closes the set and matches symmetric-group composition on two
letters. ∎

**Numbers-free statement.** The theorem above speaks of "two
elements" (identity and swap) and "a two-element group". We do
not yet measure Raw at any numerical level; "two" here counts
*Raw-endomorphisms we just constructed*, not Raw terms. Naming
this group `ℤ/2` is convenient shorthand — the structure is
Raw-intrinsic and requires no Lens. The name `ℤ/2` acquires its
quantitative content (order-2 cyclic group) once a Lens is
chosen (§3–§4).

**Lean coverage.** `Raw.swap_swap`, `Raw.swap_comp_swap`, and
`Raw.swap_ne_id` together formalise the algebraic content of
Thm 2.5 on `{id, swap}`. The full classification "every
Raw-automorphism is `id` or `swap`" is prose-only.

---

## 3. Self-recognition from within the space

The axiom produces the space `Raw` (§1) and its structural
symmetry `Aut(Raw) ≅ ℤ/2` (§2); no further structure is
axiomatically supplied. An *object* in this space is a particular
Raw term.

For such an object to recognise itself **from within the space
it inhabits** — to distinguish itself from the other Raw terms
surrounding it — it must project Raw onto a measurable codomain.
This projection is a *Lens*. The axiom does not supply the Lens;
the observer chooses it. The choice, however, is not free: the
Lens must respect Raw's structural facts, otherwise its image
does not correspond to the space the observer is in.

§3 formalises the Lens structure and records the five structural
constraints Raw-as-a-space imposes on any self-recognising Lens
(R1–R5, §3.2). The constraints are *structural consequences of
Raw's properties*; each is given in both Raw language (the
language the axiom uses) and the standard algebra shorthand.
Full derivation from Raw alone is possible but deferred.

**Definition 3.1 (Lens).** A Lens is a tuple `(α, base_a, base_b,
combine)` with `view : Raw → α` defined recursively:

```
  view a               := base_a
  view b               := base_b
  view (slash x y h)   := combine (view x) (view y).
```

The kernel `L.equiv x y := L.view x = L.view y` is the only
notion of equality on Raw the framework admits.

### 3.2 Structural constraints R1–R5

All five constraints below are structural consequences of Raw's
properties. Each is stated in two equivalent ways: **Raw
language** (describing the condition in the axiom's own
vocabulary of terms, combine, and swap) and **algebra
language** (the conventional algebraic shorthand).

**(R1) Binary combine.**

- *Raw language:* there is a rule taking Raw terms to codomain
  values via `view`, and a rule for combining two codomain
  values into a new codomain value, `combine : α² → α`.
- *Algebra:* the codomain carries a binary operation.

**(R2) Recursive faithfulness.**

- *Raw language:* the combine rule follows Raw's recursive
  structure — `view (slash x y h) = combine (view x) (view y)`.
- *Algebra:* `view` is a homomorphism of the free commutative
  magma (no fixed points) into `(α, combine)`.

**(R3) Non-vanishing.**

- *Raw language:* if `view x` and `view y` are both present
  (nonzero in `α`), then `combine (view x) (view y)` is also
  present (nonzero). Projecting a Raw term that exists never
  yields "not there".
- *Algebra:* combine has no zero divisors.

(Lean: `E213.Meta.LensCatalog.NonVanishing`.)

**(R4) Swap matches exactly one nontrivial involution.**

- *Raw language:* on the codomain `α` there is a function
  `conj : α → α` such that
  - `conj (conj u) = u` for every `u`,
  - `conj ≠ id`,
  - `view (swap r) = conj (view r)` for every `r`.
  The condition names the unique self-correspondence on `α`
  that matches `Raw.swap`.
- *Algebra:* `Aut(Raw) ≅ Aut_ℝ(α)` as groups
  (the induced group homomorphism is an isomorphism).

(Lean: `E213.Meta.LensCatalog.SwapMatching`.)

**(R5) Minimal continuous distinguishing codomain.**

- *Raw language:* different Raw terms project to different
  values in `α` (injectivity of `view`); `α` is the smallest
  connected / continuous codomain on which this is possible.
- *Algebra (post-construction):* the injectivity requirement
  picks out a continuous ℝ-algebra; the minimality clause
  identifies it with `ℝ`.

(Lean: `E213.Meta.LensCatalog.Distinguishing` captures the
injectivity half. The continuity / minimality clause of R5 is
not expressible in Lean 4 core; the identification with `ℝ` is
recorded at the prose level.)

**Summary.** R1, R2 are built into the Lens structure and its
view function (Def 3.1). R3–R5 are predicates on Lenses,
formalised in `E213.Meta.LensCatalog`.

- (R1) ⟵ Raw's constructor signature (`slash : Raw² → Raw`);
- (R2) ⟵ Raw's free-inductive generation;
- (R3) ⟵ Raw's term-level distinctness;
- (R4) ⟵ `Aut(Raw) ≅ ℤ/2` (§2 invariant);
- (R5) ⟵ Raw's term-level distinguishability + continuity.

**Working definition.** A Lens satisfying R1–R5 is called a
*self-recognising Lens*. §4 shows R1–R4 force the codomain to
be an ℝ-algebra with the prescribed swap involution, and R5
pins down the ℝ-algebra to `ℂ`.

**Theorem 3.5 (Catamorphism compatibility, symmetric case).**
For a Lens with symmetric `combine`, the view satisfies
`view (slash x y h) = combine (view x) (view y)`. Non-symmetric
`combine` admits no such view, because `slash x y h = slash y x h'`
forces commutativity on the image. (Lean:
`E213.Firmware.Raw.fold_slash`.) In particular, (R2) uniformity
forces `combine` to be commutative whenever it is extended across
the axiom's symmetric reading.

### 3.6 Lens catalogue — free choice, divergent mathematics

Any Lens whose combine satisfies (R2)'s uniformity is admissible;
different choices extract different mathematics from the same
Raw. The Lens's visibility of `swap` partitions the catalogue:

**Swap-blind lenses** identify `base_a = base_b`; consequently
`L.view (swap r) = L.view r` for every `r`. The ℤ/2 symmetry
of §2 disappears in the image. Examples:

- `Lens.depth : Raw → ℕ` with `⟨0, 0, (a, b) ↦ 1 + max a b⟩` —
  a height function. (Lean: `E213.Meta.LensCatalog.
  depth_swap_invariant`.)
- `Lens.leaves : Raw → ℕ` with `⟨1, 1, +⟩` — a size function.
  (Lean: `E213.Meta.LensCatalog.leaves_swap_invariant`.)

Extracting Peano arithmetic or any swap-agnostic counting theory
from Raw proceeds through lenses of this kind; the Lens is a
functor from Raw's bootstrapping into ℕ-valued measurement.

**Swap-visible lenses** have `base_a ≠ base_b`; `swap` then acts
nontrivially on the image. The canonical example within Lean 4
core (without complex numbers) is the ℤ-valued "signed" Lens
`⟨1, -1, +⟩`, under which `swap` becomes negation:

```
  signedLens.view (swap r) = - signedLens.view r
```

(Lean: `E213.Meta.LensCatalog.signedLens`, `signed_swap_neg`.)

This is the integer-level analogue of the ℂ-Lens of §4, where
`swap` lifts to complex conjugation.

**Characterisation.** The swap-blind / swap-visible distinction
corresponds exactly to the base values:

```
  (∀ r, L.view (swap r) = L.view r)  ⟹  L.base_a = L.base_b.
```

(Lean: `E213.Meta.LensCatalog.swap_invariant_base_eq`.)

The free choice of Lens is thus the free choice of *which
aspects of Raw to resolve*: a single-valued base erases the
axiomatic `a ↔ b` asymmetry, while a two-valued base preserves
it. §4 asks the sharp version of this choice: which Lens sees
`Raw` as completely as the axiom permits?

---

## 4. The self-recognising Lens is `ℂ`

§3 identified R1–R5 as structural constraints any self-recognising
Lens must respect. §4 translates them into algebraic conditions
on the codomain and shows the resulting class is singleton. The
natural sub-structure is two-step:

- **R1, R2, R3, R5 together force the continuous base `ℝ`.** R1
  supplies the binary operation; R2 requires a homomorphism; R3
  prohibits zero divisors; R5 forces a connected / continuous
  codomain distinguishing all Raw terms. The minimal continuous
  ℝ-algebra with no zero divisors is the field `ℝ`.
- **R4 extends `ℝ` to `ℂ`.** `Aut_ℝ(ℝ) = {id}` is trivial; R4
  requires a nontrivial involution, which `ℝ` cannot supply. The
  minimal extension carrying exactly one nontrivial involution
  is `ℂ = ℝ[i]`, with the involution given by complex
  conjugation.

### 4.1 Deriving the codomain conditions

**(F1) Finite-generated / finite-dimensional over ℝ.** Raw is
generated from two base tokens `a, b` plus the single binary
operator `slash`. A catamorphism `L.view`
maps Raw into the subalgebra of the codomain generated by
`L.base_a, L.base_b` under `L.combine`. **That subalgebra is
finitely generated.** If the codomain is an ℝ-algebra, finitely
generated ℝ-algebra + (R4)'s group-isomorphism requirement force
it to be finite-dimensional: an infinite-dimensional ℝ-algebra
carries a larger automorphism group (typically uncountable), so
(R4) fails. (F1) is thus a consequence of (R2) finite tools +
(R4) Aut faithfulness.

**(F2) Commutative.** (R4) requires `Aut_ℝ(codomain) ≅ ℤ/2`.
The quaternions `ℍ` have `Aut_ℝ(ℍ) ≅ SO(3)`, a Lie group of
dimension 3, which does not match ℤ/2. Any non-commutative
finite-dimensional ℝ-division-algebra has a similarly rich Aut
group. Commutativity of `combine` — also seen structurally as
the symmetric reading of the axiom (§3.5) — is therefore enforced
by (R4).

**(F3) Unital, as a consequence of (F2)+(R3).** A
finite-dimensional commutative division ℝ-algebra is a field, and
in particular unital. Unital-ness is not an independent
stipulation; it follows once (F2) and (R3) have placed the
codomain inside the class of ℝ-fields.

**(F4) Division (no zero divisors).** Exactly (R3): an ℝ-algebra
where some nonzero `u, v` satisfy `uv = 0` forbids the Lens from
respecting "exists" at clause (1). Split algebras like `ℝ ⊕ ℝ`
(`|Aut_ℝ| = 2`, swap) are excluded by (R3), not by unital-ness.

### 4.2 Classification and uniqueness

**Theorem 4.1 (Self-recognising Lens is ℂ).** Up to ℝ-algebra
isomorphism, the unique codomain admitting a self-recognising
Lens is the field of complex numbers `ℂ`, and under this Lens
`swap : Raw → Raw` corresponds to complex conjugation
`z ↦ z̄`.

*Proof (prose; the commutative-field-extension step is classical;
no Lean formalisation).*

By (F1)+(F2)+(F3)+(F4), the codomain is a finite-dimensional
commutative unital ℝ-algebra with no zero divisors — i.e., a
finite field extension of ℝ. Irreducible polynomials over ℝ have
degree 1 or 2 (fundamental theorem of algebra applied to `ℝ[x]`),
so `[K : ℝ] ∈ {1, 2}`.

*Dimension 1.* `K = ℝ`; `|Aut_ℝ(ℝ)| = 1`. (R4) requires
isomorphism to `Aut(Raw) ≅ ℤ/2`, of order 2. Mismatch; dim 1 is
excluded.

*Dimension 2.* `K = ℝ[α]` with `α² = -1` (the unique
2-dimensional option up to ℝ-algebra isomorphism, obtained by
adjoining a root of any monic irreducible quadratic). Any
`σ ∈ Aut_ℝ(K)` is fixed by `σ(α)`, and `σ(α)² = σ(α²) = -1`
gives `σ(α) = ±α`; so `|Aut_ℝ(K)| = 2`. The nontrivial element
is `α ↦ -α`. Under the group isomorphism required by (R4),
`swap : Raw → Raw` lifts to this `α ↦ -α` — standardly written
`z ↦ z̄` after identifying `K = ℂ` with `α = i`. ∎

**Corollary 4.2 (ℍ is not a self-recognising Lens).**
`Aut_ℝ(ℍ) ≅ SO(3)`. A group-isomorphism `ℤ/2 ≅ SO(3)` does not
exist (cardinalities and topology differ). ℍ therefore fails
(R4). Non-commutativity is the decisive obstruction.

**Corollary 4.3 (`ℝ ⊕ ℝ` is not a self-recognising Lens).**
`|Aut_ℝ(ℝ ⊕ ℝ)| = 2` (coordinate swap), so (R4) is matched;
but `(1, 0) · (0, 1) = 0` violates (R3). The split algebra
fails the "exists" condition.

### 4.3 Lean status

The arithmetic of §4 — finite ℝ-field extension classification,
Aut group computations — is classical mathematics. We do not
formalise it in Lean; no `sorry` is introduced because no §4
claim is asserted as a Lean theorem. The Lean framework
(`E213.Firmware`, `E213.Hypervisor`) formalises the Raw type, the
swap involution, and the Lens catamorphism; the specific
identification codomain = `ℂ` is recorded at the prose level.

---

## 5. Structure visible under the `ℂ` Lens

With `ℂ` fixed as the self-recognising Lens, we may now speak of
*measurable* attributes of Raw terms. Each of the following is
visible *only* through `ℂ` (or a general Lens into ℕ, which
projects the ℂ picture); none is a property of Raw alone.

### 5.1 Levels and sizes become visible

Under the `leaves : Raw → ℕ` Lens (`base_a = base_b = 1`,
`combine = +`), a Raw term acquires a natural-number "size":
the number of base tokens used to build it. Similarly, `depth`
is the Lens `(0, 0, fun a b ↦ 1 + max a b)`.

These Lenses are ℝ-algebra-trivial projections of the `ℂ`
Lens via `Re` and `dim`-like maps, so they inherit the
self-recognition pedigree of `ℂ`. We record them as distinct
Lenses for convenience; they do not add information.

The closure by levels now has numerical content:

- **Level 0:** `{a, b}` — 2 terms, each of size 1.
- **Level 1:** add `a/b`, size 2 — 3 terms total.
- **Level 2:** add `a/(a/b), b/(a/b)`, each of size 3 — 5 terms
  total.

The five Level-≤2 terms split by size as `3 + 2`:

```
A-type (sizes ≤ 2): {a, b, a/b}        — 3 terms
B-type (size 3):    {a/(a/b), b/(a/b)} — 2 terms
```

(Lean: `E213.Firmware.Raw.level1_card`,
`Raw.level2_new_card`, `Raw.level2_total_card`; 5 terms
formalised as an explicit list with `List.Nodup` by `decide`.)

### 5.2 Atom set `{2, 3}` is visible

Under the `ℂ` lens, sizes are integers; partitioning a Raw
collection into minimal blocks asks which integers are
*non-decomposable as sums of parts ≥ 2*. The lower bound `≥ 2`
is the size at which the `slash` constructor first contributes:
a bare base token has size 1 and does not exercise `slash`.
Under `ℂ`, this threshold is where the binary combine activates.

**Proposition 5.1 (Characterisation of `{2, 3}`).** An integer
`n ≥ 2` cannot be written `n = n_1 + ⋯ + n_k` with `k ≥ 2` and
each `n_i ≥ 2` iff `n ∈ {2, 3}`.

*Proof.* (Lean: `E213.OS.NonDecomposable.non_decomposable_iff`.)
A multi-part decomposition collapses to 2 parts. Case analysis:
`n ∈ {2, 3}` gives `a + b ≥ 4 > n`, impossible; `n = 4` is
`2 + 2`; `n ≥ 5` is `2 + (n - 2)` with `n - 2 ≥ 3`. ∎

The atom set is therefore `{2, 3}` — the non-decomposable sizes
post-`ℂ`. Both values are already visible in Raw's closure:
`|{a, b}| = 2` and `|{a, b, a/b}| = 3`. (Lean:
`E213.OS.PrimitiveSizes.primitive_sizes_eq_nondecomposable`.)

### 5.3 Atomic decomposition observes odd multiplicity

Under the `ℂ` Lens, a partition of a Raw collection into blocks
of sizes `{2, 3}` takes the form `n = 2a + 3b`. The Level-2
closure itself realises `(a, b) = (1, 1)` — one 3-block
(A-type) and one 2-block (B-type). Both coefficients are odd.

**Observation 5.2 (Alive).** At Level 2 of Raw's closure, each
atom type appears with multiplicity 1, an *odd* number. Paired
copies of a structurally identical atom would coincide under the
canonical-form encoding (§1.2) and collapse; only odd residues
remain. We call `(a, b)` *alive* iff both are odd. Level 2 is
alive by construction.

No external postulate has entered. "Alive" names the observed
parity pattern of Level 2 under the `ℂ` lens.

**Definition 5.3 (Atomic).** `n` is *atomic* iff `n = 2a + 3b`
has a unique solution `(a, b) ∈ ℕ²` and that solution is alive.

**Theorem 5.4 (Atomicity).** `n ∈ ℕ` is atomic iff `n = 5`.

*Proof.* (Lean: `E213.OS.Atomicity.atomic_iff_five`.)

*Existence at `n = 5`.* `3b ≤ 5` gives `b ∈ {0, 1}`; `b = 0` is
impossible; `b = 1` gives `a = 1`. Unique, alive.

*Only `n = 5`.* Bézout shift `(a, b) ↦ (a ± 3, b ∓ 2)` preserves
`2a + 3b`. `a ≥ 3` ⟹ `(a - 3, b + 2)` is a second decomposition;
`b ≥ 2` ⟹ `(a + 3, b - 2)` likewise. Hence `a < 3`, `b < 2`.
With `a, b` odd nonnegative: `a = b = 1`, `n = 5`. ∎

**Corollary 5.5.** The unique atomic `n` gives the partition
`V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2` — matching the Level-2
closure of §5.1 exactly.

### 5.4 Pair Forcing: `(2, 3)` is the unique coprime option

**Definition 5.6 (Count).** For `p, q ≥ 2`,
`count(p, q) := ⌊p/2⌋ · ⌊q/2⌋`.

*Combinatorial reading.* Under Bézout uniqueness
(`a < q ∧ b < p`), odd-positive solution pairs to `pa + qb = n`
number `⌊p/2⌋ · ⌊q/2⌋`. The bijection "atomic `n` count =
`⌊p/2⌋·⌊q/2⌋`" for general `(p, q)` is not formalised in Lean;
Theorem 5.7 is stated as a pure arithmetic identity.

**Theorem 5.7 (Pair Forcing).** For coprime `p, q` with
`2 ≤ p < q`:
```
  count(p, q) = 1  ⟺  (p, q) = (2, 3).
```

*Proof.* `⌊p/2⌋, ⌊q/2⌋ ≥ 1`; product 1 iff both equal 1;
`⌊k/2⌋ = 1 ⟺ k ∈ {2, 3}`; with `p < q` coprime, `(p, q) = (2, 3)`
uniquely. ∎ (Lean: `E213.OS.PairForcing.count_eq_one_iff`.)

**Corollary 5.8 (Convergence).** The values `(p, q) = (2, 3)` and
`n = 5` are simultaneously the non-decomposable pair of §5.2, the
atomic count of §5.3, and the unique `count = 1` coprime pair of
§5.4. Three independent arithmetic routes under the `ℂ` lens
converge on the same numbers.

---

## 6. The `(3, 2)` partition and block structure

From §5.1 (Level-2 closure) and §5.3 (atomic decomposition), Raw
measured under the `ℂ` lens carries the partition
`V = V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2`. §6 formalises the
symmetry structure on this partition.

Take `V := Fin 5`, `V_A := {0, 1, 2}`, `V_B := {3, 4}`.

**Definition 6.1.** `isA : Fin 5 → Bool`, `isA i := (i.val < 3)`.

**Definition 6.2 (Block-pair classifier).**
`classify : Fin 5 × Fin 5 → BlockPair` with six cases:

```
AAdiag    3 pairs   AAoff   6 pairs    AB    6 pairs
BA        6 pairs   BBdiag  2 pairs    BBoff 2 pairs
                                       — total 25 = |V|²
```

**Definition 6.3 (Partition-preserving permutation).** Bijection
`σ : Fin 5 → Fin 5` with `isA (σ i) = isA i` for all `i`. The
group of such bijections is `S_{V_A} × S_{V_B} ≅ S_3 × S_2`,
order 12.

**Definition 6.4 (Block-constant weight).**
`W : Fin 5 × Fin 5 → α` *block-constant* iff it factors through
`classify`.

**Theorem 6.5 (Block-constancy ⟹ invariance).** Block-constant
`W` is invariant under every partition-preserving bijection.

*Proof.* `classify` is invariant; `W = f ∘ classify`. ∎
(Lean: `E213.App.Simplex.block_constant_implies_aut_invariant`.)

**Theorem 6.6 (Invariance ⟹ block-constancy).** Prose only,
not formalised in Lean: `S_3` acts transitively on 6 ordered
distinct pairs of `V_A` (free, `|S_3| = 6`), `S_2` on 2 ordered
distinct pairs of `V_B`, and each factor on its diagonal;
invariance collapses each class.

---

## 7. Signature meta-analysis

§1 fixed `(Fin 2, binary)` from the axiom's clauses directly.
§7 is a convergence sanity-check: among generalised signatures
`RawNk (N, k)` with a pairwise-distinctness rule at the relation
level (a rule the axiom does not supply), the minimal
non-degenerate non-vacuous signature is `(N, k) = (2, 2)`.

**Definition 7.1 (Generalised Raw).**
```
inductive RawNk (N k : Nat)
  | object : Fin N → RawNk
  | rel    : (Fin k → RawNk) → RawNk
```
with reachability `∀ i, Reachable (f i)` and
`∀ i j, i ≠ j → f i ≠ f j`.

**Lemma 7.2 (Pigeonhole).** For `N < k`, no injection
`Fin k → Fin N` exists. (Lean: `E213.OS.Pigeonhole.no_inj_lt`.)

**Theorem 7.3 (Vacuousness).** In `RawNk N k` with `N < k`,
every Reachable term is a base object. (Lean:
`E213.OS.ArityForcingGeneral.reachable_base_only`.)

**Corollary 7.4 (Minimal signature).** Non-vacuity requires
`N ≥ k`; `k ∈ {0, 1}` is degenerate (constants / linear
chains). The minimal non-degenerate non-vacuous signature is
`(N, k) = (2, 2)`.

**Scope.** §7's "forced" reads inside the imported distinctness
hypothesis. §1 independently fixes `(Fin 2, binary)` from the
axiom; §7 is a convergence confirmation, not an alternative
derivation.

---

## Conclusion

The minimal system defined by the 3-clause axiom consists of the
following structure, in strict logical dependency order:

**Firmware (§§1–2):**

1. **[✓]** `Raw`, the free commutative magma on two generators
   with no fixed points (Def 1.1). Lean 4 core realisation:
   canonical-form subtype of a free ordered magma. No number, no
   size, no equality primitive.

2. **[partial]** `Aut(Raw) ≅ ℤ/2` via the swap involution
   (§2, Thm 2.5). Formalised: `Raw.swap, swap_swap,
   swap_comp_swap, swap_ne_id`. Full classification prose-only.

**Lens question and its answer (§§3–4):**

3. **[prose]** Self-recognition of a Raw term from within the
   space imposes four structural constraints on any Lens —
   binary combine, uniformity, non-degeneracy, Aut-faithfulness.
   Each constraint is read off Raw as a space (its constructor,
   its free generation, its term distinctness, its invariant),
   not off the axiom clauses (§3.4).

4. **[prose]** The unique codomain satisfying all four is `ℂ`
   (§4 Thm 4.1). The argument is classical finite ℝ-field
   extension theory; not formalised in Lean. ℍ excluded by Aut
   mismatch (§4 Cor 4.2); `ℝ ⊕ ℝ` excluded by non-degeneracy
   (§4 Cor 4.3).

**Structure visible under `ℂ` (§§5–6):**

5. **[✓]** Under the `ℂ` Lens (and its ℕ-projections), sizes
   become visible: 5 Raw terms at Level ≤ 2, split 3 + 2 (§5.1);
   atom set `{2, 3}` from non-decomposability (§5.2 Prop 5.1);
   atomic decomposition with both coefficients odd (§5.3 Obs 5.2);
   unique atomic `n = 5` (§5.3 Thm 5.4).

6. **[✓]** Pair Forcing: `(2, 3)` is the unique coprime pair with
   `2 ≤ p < q` satisfying `count(p, q) = 1` (§5.4 Thm 5.7);
   three routes converge (§5.4 Cor 5.8).

7. **[partial]** `(3, 2)` partition of `V = Fin 5`; `S_3 × S_2`
   invariance equivalent to block-constancy (§6 Thms 6.5–6.6).
   Lean formalises the forward direction.

**Meta-confirmation (§7):**

8. **[✓ under imported distinctness]** `(N, k) = (2, 2)` is the
   minimal non-degenerate non-vacuous signature for generalised
   `RawNk` (§7 Thm 7.3, Cor 7.4).

---

### No stipulations.

We list every condition introduced in the body and identify its
source:

| Condition                         | Source                          |
| --------------------------------- | ------------------------------- |
| anti-reflexive (`no x/x`)         | axiom clause (2), semantic      |
| symmetric (`x/y = y/x`)           | axiom clauses (2–3), semantic   |
| `Aut(Raw) ≅ ℤ/2`                  | Raw's symmetric base roles      |
| R1: binary combine                | Raw's `slash` constructor       |
| R2: recursive faithfulness        | Raw's free-inductive structure  |
| R3: non-vanishing                 | Raw's term-level distinctness   |
| R4: swap matches one involution   | §2 Aut(Raw) invariant of space  |
| R5: distinguishing + continuous   | Raw's term-level distinguishability |
| codomain = `ℝ` (from R1+R2+R3+R5) | minimal continuous no-zero-div  |
| codomain = `ℂ` (from + R4)        | minimal extension with ℤ/2 aut  |
| `atom ≥ 2`                        | threshold where `slash` acts    |
| atom values `{2, 3}`              | Prop 5.1 arithmetic             |
| alive (both odd)                  | Obs 5.2 of Level-2 closure      |
| `n = 5` atomic                    | Thm 5.4 under `ℂ` lens          |
| `(3, 2)` partition                | Level-2 closure + Thm 5.4       |

Every row's source is one of: an axiom clause, a structural fact
of Raw as a space (for R1–R5), a theorem derived from those, or
an observation made after the `ℂ` lens is in place. **No row is
an external stipulation.**

This is the minimal system defined by the 3-clause axiom.

End.
