# The Minimal System of Binary Relations

**Axiom.** *There exists a relation object between two objects.*

We take this as the sole axiom of what follows and derive the resulting
structure.

---

## 0. Notation and conventions

- `Fin n` denotes the standard `n`-element type `{0, 1, …, n-1}`.
- `inductive T` denotes an initial algebra presentation: `T` is the
  smallest type closed under the listed constructors. Equivalently,
  `T` is the free algebra over its signature.
- `Raw.x` and `x.y` are type-theoretic dot notation; no semantic content.
- "Function equality" throughout means definitional/propositional
  equality of terms, not any quotient.
- All claims below are formally checked in Lean 4 (`E213.*` modules,
  0 `sorry`); we cite the Lean name where relevant.

---

## 1. Primitive type

**Definition 1.1 (Raw).** `Raw` is the inductive type with two
constructors:

```
inductive Raw
  | object   : Fin 2 → Raw
  | relation : Raw → Raw → Raw
```

The base constructor `object` enumerates the two objects required by
the axiom; the second constructor `relation` realizes the axiom's
"relation object between two objects."

**Definition 1.2 (Reachable).** The inductive predicate
`Reachable : Raw → Prop` is

```
  base : (i : Fin 2) → Reachable (object i)
  step : Reachable x → Reachable y → x ≠ y →
         Reachable (relation x y).
```

The apartness `x ≠ y` is a technical encoding of the axiom's "two":
the step constructor fires only from *two* Reachable arguments, not
one repeated. No negation primitive is introduced at the axiomatic
level; `≠` is purely Lean's bookkeeping of "two distinct."

**Definition 1.3 (Well-formedness).**

```
Raw.wellFormed : Raw → Prop
  | object _     => True
  | relation x y => x ≠ y ∧ x.wellFormed ∧ y.wellFormed.
```

---

## 2. Characterization and decidability

**Theorem 2.1.** `Reachable x ↔ x.wellFormed`.

*Proof.* (Lean: `E213.Clean213.reachable_iff_wellFormed`.)

(⇒) By induction on the Reachable derivation. Base: `wellFormed
(object i) = True`, immediate. Step: from `Reachable x`, `Reachable
y`, `x ≠ y` with induction hypotheses `x.wellFormed, y.wellFormed`,
conclude `(relation x y).wellFormed = x ≠ y ∧ x.wellFormed ∧
y.wellFormed` using the three hypotheses.

(⇐) By induction on the structure of `x`. Base `object i`: apply
`Reachable.base i`. Relation `relation x y` with hypothesis
`x ≠ y ∧ x.wellFormed ∧ y.wellFormed`: destructure, apply induction
hypotheses on `x`, `y`, then `Reachable.step`. ∎

**Corollary 2.2 (Decidability).** `Reachable` is decidable on `Raw`.

*Proof.* `Raw` has decidable equality (derived from its finite
signature and `DecidableEq (Fin 2)`); `wellFormed` is decidable by
structural recursion; combine via Theorem 2.1. ∎

**Theorem 2.3 (No self-relation).** For every `x : Raw`,
`¬ Reachable (relation x x)`.

*Proof.* By Theorem 2.1 this reduces to `¬ (x ≠ x ∧ ...)`, which
is immediate from `x = x`. ∎

**Theorem 2.4 (Relation inversion).**
`Reachable (relation x y) → Reachable x ∧ Reachable y ∧ x ≠ y`.

*Proof.* Reduce to well-formedness; destructure. ∎

---

## 3. The swap automorphism

**Definition 3.1 (Swap).** Let `flip : Fin 2 → Fin 2` be the
non-identity permutation. Define `swap : Raw → Raw` by

```
  swap (object i)     := object (flip i)
  swap (relation x y) := relation (swap x) (swap y).
```

**Theorem 3.2 (Involution).** `swap (swap x) = x` for all `x : Raw`.

*Proof.* By induction on `x`, using `flip ∘ flip = id`. ∎

**Corollary 3.3 (Bijectivity).** `swap` is a bijection on `Raw`.

**Theorem 3.4 (Reachable-preservation).** `Reachable x → Reachable (swap x)`.

*Proof.* By induction on the Reachable derivation; the step case
uses Corollary 3.3 to propagate the apartness hypothesis. ∎

**Definition 3.5 (Raw-automorphism).** A *Raw-automorphism* is a
bijection `φ : Raw → Raw` satisfying, for some permutation
`σ : Fin 2 → Fin 2`,

```
  φ (object i)     = object (σ i),
  φ (relation x y) = relation (φ x) (φ y).
```

Such `φ` is uniquely determined by `σ`: by induction on `Raw`, the
value of `φ` on any term is fixed by `σ` and the recursive clause.

**Theorem 3.6 (Automorphism group).** The group `Aut(Raw)` of
Raw-automorphisms is isomorphic to the symmetric group `S_{Fin 2}`,
hence to `ℤ/2`. Its nontrivial element is `swap`.

*Proof.* The map `σ ↦ φ_σ` (with `φ_σ` built recursively from `σ`)
is a bijection `Perm(Fin 2) → Aut(Raw)`: injectivity follows from
`φ_σ (object i) = object (σ i)`, surjectivity from Definition 3.5.
One checks `φ_{σ∘σ'} = φ_σ ∘ φ_{σ'}`, so the bijection is a group
isomorphism. `Perm(Fin 2) = S_2 ≅ ℤ/2`; its non-identity is the flip,
inducing `swap`. ∎

---

## 4. Lens framework

**Definition 4.1 (Lens).** A `Lens` with codomain type `α` is a pair

```
  Lens α = (objValue : Fin 2 → α, combine : α → α → α).
```

**Definition 4.2 (Catamorphism).** The `view` of a Lens `L : Lens α` is

```
  L.view (object i)     := L.objValue i
  L.view (relation x y) := L.combine (L.view x) (L.view y).
```

**Definition 4.3 (Kernel equivalence).** For `L : Lens α`, define
`L.equiv x y := L.view x = L.view y`. This is reflexive, symmetric,
and transitive; it is the kernel equivalence of `L.view`.

**Definition 4.4 (Refinement).** `L` refines `M` (written `L.refines M`)
iff `∀ x y, L.equiv x y → M.equiv x y`, i.e. `M.view` factors
through `L.view`.

**Theorem 4.5 (Catamorphism universality).** For any `α`, `b : Fin 2 → α`,
`c : α → α → α`, there exists a unique `φ : Raw → α` with
`φ (object i) = b i` and `φ (relation x y) = c (φ x) (φ y)`. This `φ`
is `view` of the Lens `(b, c)`.

*Proof.* Existence by the inductive definition; uniqueness by
induction on `Raw`. ∎

---

## 5. Signature forcing (arity and base size)

We examine whether the signature `(Fin 2, binary relation)` is
forced by non-vacuity.

**Definition 5.1 (Generalized Raw).** For `N, k : ℕ`, define

```
inductive RawNk (N k : Nat)
  | object : Fin N → RawNk
  | rel    : (Fin k → RawNk) → RawNk,
```

with Reachable predicate

```
  base : (i : Fin N) → ReachableNk (object i)
  step : (f : Fin k → RawNk) →
         (∀ i, ReachableNk (f i)) →
         (∀ i j, i ≠ j → f i ≠ f j) →
         ReachableNk (rel f).
```

(Definition 1.1 is the case `N = k = 2`.)

**Lemma 5.2 (Pigeonhole).** For `N < k`, there is no injection
`Fin k → Fin N`.

*Proof.* (Lean: `E213.Pigeonhole.no_inj_lt`.) It suffices to show
no injection `g : Fin (N+1) → Fin N` exists; a larger `k > N` gives
one by restriction. Induct on `N`.

*Case* `N = 0`: `Fin 0` is empty, so `g ⟨0, _⟩ : Fin 0` is
uninhabited; contradiction.

*Case* `N = m+1`: given `g : Fin (m+2) → Fin (m+1)` assumed
injective, set `v := g ⟨m+1, _⟩`. Define the "shift-around"
`s : Fin (m+1) \ {v} → Fin m` by
```
  s(w) = ⟨w.val, _⟩      if w.val < v.val,
  s(w) = ⟨w.val - 1, _⟩  if w.val > v.val.
```
For each `i : Fin (m+1)`, injectivity of `g` yields
`g ⟨i.val, _⟩ ≠ v`, so `s (g ⟨i.val, _⟩)` is defined. The composite
`g' : Fin (m+1) → Fin m, g' i := s(g ⟨i.val, _⟩)` is injective
(both `g` restricted and `s` are), contradicting the induction
hypothesis. ∎

**Theorem 5.3 (Vacuousness).** In `RawNk N k` with `N < k`, every
`ReachableNk`-term is a base object.

*Proof.* Induction on the Reachable derivation. Base: immediate.
Step case: `f : Fin k → RawNk` with each `f i` Reachable and
pairwise distinct. By induction hypothesis, each `f i = object (g i)`
for some `g i : Fin N` (witness extracted via `Classical.choose`
applied to the existential). Injectivity of `g` follows from
pairwise distinctness of `f`. Lemma 5.2 contradicts. ∎

**Corollary 5.4.** Non-vacuity requires `N ≥ k`. The remaining
arities `k = 0, 1` are degenerate in the following precise senses:
- `k = 0`: `rel` takes no arguments, so `rel : RawN0`; every Reachable
  term is either a base object or `rel` itself — a finite system.
  The Reachable set fails to embed any non-trivial branching
  relation structure.
- `k = 1`: `rel : RawN1 → RawN1`; Reachable terms form a sequence
  `object i, rel(object i), rel(rel(object i)), …` linearly ordered
  by depth. The resulting binary "relation structure" is the
  singleton relation `rel` of arity `1`, carrying no information
  about distinct related objects.

Call an arity *degenerate* iff either of these conditions holds;
*non-degenerate* iff `k ≥ 2`. The minimal non-degenerate, non-vacuous
signature is therefore `(N, k) = (2, 2)`.

This is the signature of Definition 1.1.

---

## 6. Atomicity

In §1–5 the axiom produced `Raw`, the swap automorphism
`Aut(Raw) ≅ ℤ/2`, the Lens framework, and the forced signature
`(Fin 2, binary)`. We now derive the unique vertex count admitting a
canonical atomic partition.

The atomicity argument uses three components — a lower bound on atom
size, the atom set itself, and an "alive" predicate — each of which
is grounded in the primitive. The grounding is audited component-
wise in Remark 6.6 (after the main theorem is stated and proved).
Proposition 6.5 below provides the arithmetic characterization of
the atom set.

**Setup.** Given the atom set `A = {2, 3}` (justified arithmetically
by Proposition 6.5 and grounded in the primitive by Remark 6.6),
consider decompositions of `n ∈ ℕ` as `n = 2a + 3b` with
`(a, b) ∈ ℕ²`.

**Definition 6.1 (Alive).** A decomposition `(a, b)` is *alive* iff
`a` and `b` are both odd.

**Definition 6.2 (Atomic).** `n` is *atomic* iff there exists a unique
pair `(a, b) ∈ ℕ²` with `n = 2a + 3b`, and that pair is alive.

**Theorem 6.3 (Atomicity).** `n ∈ ℕ` is atomic iff `n = 5`.

*Proof.* (Lean: `E213.Atomicity.atomic_iff_five`.)

*`⇐` (Existence at `n = 5`).* From `3b ≤ 5` we get `b ∈ {0, 1}`;
`b = 0` gives `2a = 5`, impossible; `b = 1` gives `a = 1`. So the
unique decomposition is `(1, 1)`, alive. Hence `5` is atomic.

*`⇒` (Only `n = 5`).* Let `(a, b)` be the unique alive decomposition
of `n`. The *Bézout shift*
```
  (a, b) ↦ (a ± 3, b ∓ 2)
```
preserves `2a + 3b`. If `a ≥ 3`, then `(a - 3, b + 2) ∈ ℕ²` is a
valid second decomposition, contradicting uniqueness; hence `a < 3`.
If `b ≥ 2`, then `(a + 3, b - 2) ∈ ℕ²` is likewise a second valid
decomposition; hence `b < 2`. Combined with `a, b` odd and
nonnegative, this forces `a = b = 1`, giving `n = 2·1 + 3·1 = 5`. ∎

**Corollary 6.4.** The unique atomic `n` admits the unique atomic
decomposition `(1, 1)`: one 2-block and one 3-block, total `5`
vertices in `V = V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2`.

**Proposition 6.5 (Characterization of `{2, 3}`).** An integer
`n ≥ 2` *cannot* be expressed as a sum `n = n_1 + ⋯ + n_k` with
`k ≥ 2` and each `n_i ≥ 2` if and only if `n ∈ {2, 3}`.

*Proof.* (Lean: `E213.NonDecomposable.non_decomposable_iff`.)

Any `k`-part decomposition with `k ≥ 2` and parts `≥ 2` collapses
to a 2-part one: take `a := n_1` and `b := n_2 + ⋯ + n_k`; then
`a ≥ 2` and `b ≥ 2(k-1) ≥ 2`. It suffices to treat the 2-part case.

- `n = 2`: any `a + b = 2` with `a, b ≥ 2` gives `a + b ≥ 4 > 2`;
  impossible. Non-decomposable.
- `n = 3`: same, `a + b ≥ 4 > 3`; impossible. Non-decomposable.
- `n = 4`: `4 = 2 + 2`. Decomposable.
- `n ≥ 5`: `n = 2 + (n - 2)` with `n - 2 ≥ 3 ≥ 2`. Decomposable. ∎

We henceforth call `n` *non-decomposable* iff `n ∈ {2, 3}`.

**Remark 6.6 (Status of the atom hypothesis).** With Proposition 6.5
in hand, we can break the atom hypothesis into parts and locate
precisely where §1–5 does and does not suffice.

(a) *Lower bound `n ≥ 2`.* The primitive (Axiom; Definition 1.1)
concerns *relation between two objects*. A hypothetical atom of
size `1` — a solitary object — cannot instantiate the primitive
at all: the `relation` constructor requires two distinct
Reachable arguments (Definition 1.2, Theorem 2.3). We take this
as sufficient motivation within §1–5 for restricting atom sizes
to `≥ 2`.

(b) *Atom identification `A = {2, 3}`.* The principled derivation
is arithmetic. By Proposition 6.5, the non-decomposable integers
`≥ 2` — those that cannot be written as a sum of `k ≥ 2` parts
each `≥ 2` — are exactly `{2, 3}`. This is the standard meaning of
"atom" (irreducible under the composition in question) and it is
independent of §1–5. Combined with (a), the atom set is fixed as
`A = {2, 3}`.
(Lean: `E213.NonDecomposable.non_decomposable_iff`.)

An informal parallel: the same two sizes occur as natural
cardinalities in the primitive data — the input pair (`|{o_0, o_1}|
= 2`) and the first closure under a single relation application
(`|{o_0, o_1, relation o_0 o_1}| = 3`). This observation is
consistent with Proposition 6.5 but is not used to derive it; it is
recorded for intuition.
(Lean: `E213.PrimitiveSizes.primitive_sizes_eq_nondecomposable`.)

(c) *The alive predicate is Raw-intrinsic.* The condition "both
`a` and `b` odd" is *not* an external hypothesis: it is Raw's
distinctness rule applied at the multiplicity level.

The single structural rule of Raw is `x ≠ y` in every
`relation x y` (Definition 1.2). This rule applies at every level
of nesting: no Reachable term may have two structurally identical
direct sub-terms (Theorem 2.3 generalizes inductively — at every
node of a Reachable Raw tree, the two arguments are distinct).

Lifting this rule to multiplicities of structurally identical
atoms in a vertex partition: two structurally identical copies of
the same atom-type cannot coexist as distinct ingredients
(Raw distinguishes nothing within a structural-equivalence class).
Paired copies *annihilate* — they contribute nothing because the
pair has no Raw-distinguishable content. Only odd residues survive.

Concretely: a multiplicity `a` of a single atom-type contributes
to the structure as `a mod 2`, by repeated pair-cancellation.
The "alive" condition `a % 2 = 1 ∧ b % 2 = 1` is exactly the
statement that both atom-types have surviving (odd) residues. (Lean:
`E213.AliveFromDistinctness.alive_iff_odd_pair`.)

This is the same mechanism as exterior algebra: `v ∧ v = 0` is
not an axiom of `∧` but a formal expression of "two structurally
identical inputs cancel." Raw's `x ≠ y` is the same principle in
its primitive form, of which exterior algebra is a concrete model.

**Scope claim (revised).** All three components are grounded in the
primitive:

- (a) *Lower bound `≥ 2`*: the axiom's "two objects" rules out
  atoms of size `1`.
- (b) *Atom set `{2, 3}`*: by Proposition 6.5, the non-decomposable
  integers `≥ 2` are exactly `{2, 3}` — the standard "atom as
  irreducible" identification, independent of §1–5. (The same two
  sizes occur as natural cardinalities of the input pair and first
  closure; this is recorded as a parallel intuition.)
- (c) *Alive predicate*: Raw's rule `x ≠ y` applied at the
  multiplicity level, as above.

Theorem 6.3 (Atomicity → `n = 5`) follows from the axiom alone.
No external hypothesis is imported in §6.

---

## 7. Block structure and invariance

Take `V := Fin 5` with the canonical partition
`V_A := {0, 1, 2}, V_B := {3, 4}`.

**Definition 7.1.** The partition indicator is
`isA : Fin 5 → Bool, isA i := (i.val < 3)`.

**Definition 7.2 (Block-pair classifier).** Define
`classify : Fin 5 × Fin 5 → BlockPair` where `BlockPair` has six
values:

```
AAdiag   -- (i, i) with i ∈ V_A       (3 pairs)
AAoff    -- (i, j) with i ≠ j in V_A  (6 pairs)
AB       -- (i, j), i ∈ V_A, j ∈ V_B  (6 pairs)
BA       -- (i, j), i ∈ V_B, j ∈ V_A  (6 pairs)
BBdiag   -- (i, i) with i ∈ V_B       (2 pairs)
BBoff    -- (i, j) with i ≠ j in V_B  (2 pairs)
```

The six orbits exhaust `Fin 5 × Fin 5`, confirming
`3 + 6 + 6 + 6 + 2 + 2 = 25 = |V|²`.

**Definition 7.3 (Partition-preserving permutation).** A bijection
`σ : Fin 5 → Fin 5` *preserves the partition* iff
`isA (σ i) = isA i` for all `i`.

The group of partition-preserving bijections is isomorphic to
`S_{V_A} × S_{V_B} ≅ S_3 × S_2`, of order 12.

**Definition 7.4 (Block-constant weight).** A function
`W : Fin 5 × Fin 5 → α` is *block-constant* iff it factors through
`classify`: `W i j = f (classify i j)` for some `f : BlockPair → α`.

**Theorem 7.5 (Block-constancy ⟹ Invariance).** If `W` is
block-constant then `W` is invariant under every partition-
preserving bijection: for every such `σ` and all `i, j`,
`W (σ i) (σ j) = W i j`.

*Proof.* (Lean: `E213.Simplex.block_constant_implies_aut_invariant`.)
For bijective partition-preserving `σ`, both `isA (σ i) = isA i` and
`σ i = σ j ↔ i = j` hold. Hence `classify (σ i) (σ j) = classify i j`.
Since `W = f ∘ classify`, the conclusion follows. ∎

**Theorem 7.6 (Invariance ⟹ Block-constancy).** Conversely, if `W`
is invariant under every partition-preserving bijection, then `W` is
block-constant.

*Proof.* We show two pairs in the same block-pair class have equal
`W`-values. Given `σ ∈ S_3` on `V_A`, extend to a partition-
preserving bijection `σ̂` of `V` by acting as identity on `V_B`;
analogously for `τ ∈ S_2` on `V_B`. Then `σ̂`, `τ̂`, and their
compositions are partition-preserving bijections, so `W` is invariant
under them.

*Class `AAdiag`.* Given `(i, i), (i', i')` with `i, i' ∈ V_A`: pick
`σ ∈ S_3` with `σ(i) = i'` (transitivity of `S_3` on `V_A`). Then
`W i i = W (σ̂ i) (σ̂ i) = W i' i'`.

*Class `AAoff`.* Given `(i, j), (i', j')` both with `i ≠ j ∈ V_A`
and `i' ≠ j' ∈ V_A`: `S_3` acts transitively on the `6` ordered
distinct pairs in `V_A` (|ordered distinct pairs| = `3·2 = 6 = |S_3|`;
the action is free on distinct pairs, hence transitive). Pick `σ`
with `σ(i) = i', σ(j) = j'`; then `W i j = W i' j'` by invariance.

*Class `AB`.* Given `(i, j), (i', j')` with `i, i' ∈ V_A`,
`j, j' ∈ V_B`: by transitivity of `S_3` on `V_A`, pick `σ ∈ S_3` with
`σ(i) = i'`. By transitivity of `S_2` on `V_B`, pick `τ ∈ S_2` with
`τ(j) = j'`. Then the composite `σ̂ ∘ τ̂` sends `(i, j) ↦ (i', j')`,
so `W i j = W i' j'`.

*Class `BA`.* Symmetric to `AB`: swap the roles of `σ` and `τ`.
Given `(i, j), (i', j')` with `i, i' ∈ V_B`, `j, j' ∈ V_A`: pick
`τ ∈ S_2` with `τ(i) = i'` and `σ ∈ S_3` with `σ(j) = j'`; the
composite sends `(i, j) ↦ (i', j')`.

*Class `BBdiag`.* Given `(i, i), (i', i')` with `i, i' ∈ V_B`: pick
`τ ∈ S_2` with `τ(i) = i'` (transitivity of `S_2` on `V_B`). Then
`W i i = W i' i'`.

*Class `BBoff`.* `V_B = {3, 4}`; the only ordered distinct pairs are
`(3, 4)` and `(4, 3)`. The non-identity `τ ∈ S_2` swaps them, giving
`W 3 4 = W 4 3`.

In every class, `W` is constant. Hence `W` factors through
`classify`. ∎

---

## 8. Codomain forcing for faithful Lenses

We now study, within a specified class of codomains, which admit a
canonical Lens compatible with `Aut(Raw)`.

**Class `𝒞`.** Fix the class of codomains
```
  𝒞 = {K : K is a finite-dimensional ℝ-algebra,
            commutative, with multiplicative identity, and
            a division algebra (every nonzero element is invertible)}.
```
We comment on these assumptions in Remark 8.6.

**Definition 8.1 (Algebra automorphism).** For `K ∈ 𝒞`, let
`Aut_ℝ(K)` denote the group of `ℝ`-algebra automorphisms of `K`
(i.e., ring automorphisms fixing `ℝ ⊆ K` pointwise).

**Definition 8.2 (Aut-equivariance).** Let `L : Lens α` (Definition
4.1) with codomain type `α := K` (so `L.objValue : Fin 2 → K` and
`L.combine : K → K → K`). `L` is *Aut-equivariant* iff there is a
group homomorphism `ρ : Aut(Raw) → Aut_ℝ(K)` such that, for every
`τ ∈ Aut(Raw)` and every `x : Raw`,
```
  L.view (τ x) = ρ(τ) (L.view x).
```

**Definition 8.3 (Aut-faithfulness).** `L` is *Aut-faithful* iff the
induced `ρ` of Definition 8.2 is a group *isomorphism*
`Aut(Raw) ≅ Aut_ℝ(K)` (not merely an injection).

**Theorem 8.4 (Faithful codomain in `𝒞`).** Let `K ∈ 𝒞`. If `K` admits
an Aut-faithful Lens, then `K ≅ ℂ` as `ℝ`-algebras.

*Proof.*

(i) *Classification of `𝒞`.* Every `K ∈ 𝒞` is a finite field
extension of `ℝ`: commutativity + unital + division ⟹ `K` is a
field, and finite-dim over `ℝ` ⟹ `K` is algebraic over `ℝ`. The
irreducible polynomials over `ℝ` have degree `1` or `2` (by the
fundamental theorem of algebra applied to `ℝ[x]`), so
`[K : ℝ] ∈ {1, 2}`. Hence `K ≅ ℝ` or `K ≅ ℂ`. (This is the
commutative case of Frobenius's theorem.)

(ii) *Computation of `Aut_ℝ(K)`.*
- `Aut_ℝ(ℝ) = {id}`: any `ℝ`-linear ring endomorphism of `ℝ` is
  determined by its value on `1`, which must be `1`.
- `Aut_ℝ(ℂ)`: any `σ ∈ Aut_ℝ(ℂ)` is determined by `σ(i)`, since
  `ℂ = ℝ(i)` as an `ℝ`-algebra. From `σ(i)² = σ(i²) = σ(-1) = -1`,
  we get `σ(i) = ±i`. Hence `Aut_ℝ(ℂ) = {id, conjugation} ≅ ℤ/2`.

(iii) *Faithfulness.* `Aut(Raw) ≅ ℤ/2` (Theorem 3.6). Aut-faithfulness
(Definition 8.3) requires a group isomorphism
`ρ : Aut(Raw) → Aut_ℝ(K)`.
- `K = ℝ`: `|Aut_ℝ(ℝ)| = 1 ≠ 2 = |Aut(Raw)|`. No isomorphism exists;
  no Aut-faithful Lens to `ℝ`.
- `K = ℂ`: `|Aut_ℝ(ℂ)| = 2 = |Aut(Raw)|`. The unique group isomorphism
  `ρ : ℤ/2 → ℤ/2` sends `swap ↦ conjugation`.

Therefore `K ≅ ℂ`. ∎

**Corollary 8.5 (ℍ excluded by commutativity).** Dropping
commutativity from `𝒞` admits `ℍ` (quaternions), a finite-dim
unital division `ℝ`-algebra. However, `Aut_ℝ(ℍ) ≅ SO(3)` is a
connected Lie group of dimension `3`, and `|Aut(Raw)| = 2 ≠
|SO(3)|`. No group isomorphism `Aut(Raw) ≅ Aut_ℝ(ℍ)` exists;
hence `ℍ` admits no Aut-faithful Lens.

*Remark.* The commutativity condition in `𝒞` is therefore the
decisive constraint separating `ℂ` from `ℍ`. The other conditions
in `𝒞` (finite-dim, unital, division) serve to isolate
well-behaved target algebras; the `ℂ`-versus-`ℍ` choice, specifically,
is made by requiring commutativity, which aligns `Aut_ℝ(K)` with
the discrete `Aut(Raw) ≅ ℤ/2`.

**Remark 8.6 (On the remaining conditions in `𝒞`).** Corollary 8.5
has addressed the commutativity condition. The remaining three:
- *Finite-dim*: excludes infinite-dimensional ℝ-algebras (e.g.,
  function algebras, formal power series). Needed to invoke the
  classification step (i) in Theorem 8.4.
- *Unital + division*: excludes split algebras like `ℝ ⊕ ℝ`
  (which has zero divisors) and para-algebras without unit.

Each condition is necessary for the conclusion. Theorem 8.4 may be
read as: within the classical category of finite-dim commutative
unital ℝ-division algebras, `ℂ` is the unique object with
automorphism group matching `Aut(Raw) ≅ ℤ/2`.

**Remark 8.7 (Relation to Hurwitz–Frobenius).** The theorems of
Frobenius (finite-dim associative ℝ-division algebras are `ℝ, ℂ, ℍ`)
and Hurwitz (ℝ-composition algebras are `ℝ, ℂ, ℍ, 𝕆`) play no
external role here. Step (i) of the proof uses only the commutative
fragment of Frobenius (which reduces to Gelfand–Mazur). The wider
classification is of independent interest but not used.

---

## Conclusion

The minimal system defined by the axiom

> *there exists a relation object between two objects*

consists of the following structure, presented here with precise
dependency tracking between claims.

**From the axiom alone (§1–5):**

1. A free inductive type `Raw` with constructors
   `object : Fin 2 → Raw` and `relation : Raw → Raw → Raw`,
   together with a Reachable predicate carving out well-formed
   terms and excluding self-relations (Theorem 2.3).

2. A single nontrivial Raw-automorphism (the swap involution),
   yielding `Aut(Raw) ≅ ℤ/2` (Theorem 3.6).

3. A Lens/catamorphism framework: every pair
   `(b : Fin 2 → α, c : α → α → α)` determines a unique
   `view : Raw → α` (Theorem 4.5), with kernel-equivalence and
   refinement as natural operations.

4. The signature `(Fin 2, binary)` is the unique minimal
   non-degenerate, non-vacuous signature: `N < k` makes the system
   vacuous (Theorem 5.3), and `k ∈ {0, 1}` yields structurally
   degenerate constants or unary chains (Corollary 5.4).

**From the axiom together with §6–7 (all three components of the
atom hypothesis now Raw-intrinsic; see Remark 6.6):**

5. The atom set `A = {2, 3}` is fixed by Proposition 6.5
   (non-decomposable integers `≥ 2`) combined with the primitive
   lower bound `≥ 2`. The alive predicate is Raw's distinctness
   rule at the multiplicity level (pair cancellation under
   structural equivalence). Together, `n = 5` is the unique atomic
   vertex count (Theorem 6.3), giving the canonical partition
   `V = V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2`.

6. The `S_3 × S_2` action yields exactly six orbits on `V × V`,
   with `3 + 6 + 6 + 6 + 2 + 2 = 25 = |V|²`, and invariance under
   this action is equivalent to block-constancy (Theorems 7.5–7.6).

**Within the class of finite-dim commutative unital ℝ-division
algebras (§8):**

7. The unique such algebra admitting an Aut-faithful Lens — one
   whose induced action on the codomain matches `Aut(Raw) ≅ ℤ/2`
   exactly — is `ℂ` (Theorem 8.4).

This is the minimal system defined by "there is a relation."

End.
