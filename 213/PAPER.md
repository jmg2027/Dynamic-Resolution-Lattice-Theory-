# The Minimal System of Binary Relations

**Axiom.**

1. *Something exists.*
2. *To know what it is, another something is required.*
3. *That other something is also a something.*

Clauses (1)+(3) give at least two somethings; clause (2) is the
primitive *distinction*, applied recursively. We take these three
clauses as the sole axiom and derive the resulting structure.

Reading "another" (clause 2) and "between" (clauses 2–3)
semantically:

- **Anti-reflexive:** `slash x x` is *not* a valid term;
  distinguishing `x` from `x` conveys nothing.
- **Symmetric:** `slash x y = slash y x`; "between" is
  directionless.

The treatment is organised into two layers:

- **Firmware (§1).** The type `Raw` and its three constructors,
  implementing the three axiom clauses. No equality, inequality,
  ordering, or subtree-identification is available at this layer.
- **Hypervisor (§3 and beyond).** Each `Lens L : Raw → α` supplies
  a codomain with its own notion of equality; `L.equiv x y :=
  L.view x = L.view y` is the kernel-equivalence. "Same/different"
  on `Raw` is Lens-relative.

---

## 0. Notation and conventions

- `Fin n` denotes the standard `n`-element type `{0, 1, …, n-1}`.
- `inductive T` denotes an initial algebra presentation: `T` is
  the smallest type closed under the listed constructors.
- All claims below are formally checked in Lean 4
  (`E213.*` modules, 0 `sorry`); we cite the Lean name where
  relevant. When only part of a PAPER statement is formalised, we
  mark the Lean citation "partial" or "prose only".
- The axiom does *not* supply an equality or inequality primitive
  on `Raw`. Lean's propositional equality is external bookkeeping,
  used only for case analysis. Apartness is not part of `Raw`; any
  appeal to it belongs to a Lens.

---

## 1. Firmware: the primitive type

### 1.1 Target structure

The axiom's three clauses name two initial somethings `a, b`, a
binary *distinction* operator `slash` taking two (necessarily
distinct, by clause (2)) somethings to a new something, and
recursion (clause (3): the output of `slash` is again a
something, so `slash` applies to it in turn).

**Definition 1.1 (Raw, target).** The target firmware is the
**free commutative magma on 2 generators with no fixed points** —
the unique closure of `{a, b}` under a symmetric, anti-reflexive
binary operation `slash`.

### 1.2 Lean emulation: canonical-form subtype

Lean 4's core calculus of inductive constructions does not have
primitive quotient types on arbitrary relations, and we import no
set theory (no `Multiset`, no Mathlib). We therefore *emulate* the
free-commutative-magma-without-fixed-points by a canonical-form
subtype of the free (ordered) magma. An auxiliary total order on
trees selects a unique representative per unordered pair. **The
ordering is an implementation artifact of the Lean encoding; it
does not exist in the axiom.**

```
-- Internal: the free ordered magma.
inductive Tree
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree

-- Structural lex compare (a < b < slash; within slash, lex on
-- children). Serves only to pick canonical representatives.
def Tree.cmp : Tree → Tree → Ordering

-- A Tree is canonical iff every slash node has strictly ordered
-- children. Strict ordering implies distinctness, realising
-- anti-reflexivity.
def Tree.canonical : Tree → Bool

-- Raw: the canonical subtype.
def Raw : Type := { t : Tree // t.canonical = true }
```

The smart constructor `Raw.slash : (x y : Raw) → x ≠ y → Raw`
orders the children so the result is canonical; the theorem
`Raw.slash_comm` shows both input orderings collapse to the same
Raw term — the symmetric reading of the axiom.

(Lean: `E213.Firmware.Raw.slash`, `E213.Firmware.Raw.slash_comm`.)

**Definition 1.2 (Depth).** The structural-recursive height
measure `Raw.depth : Raw → ℕ` is `0` on `a, b` and
`1 + max x.depth y.depth` on `slash x y`. It is a function on
Raw, not a predicate; it uses no equality.

### 1.3 First three closure levels

Let the *level* of a Raw term be its depth. The closure by levels
is:

- **Level 0:** `{a, b}` — 2 terms.
- **Level 1:** add `a/b`, the sole unordered distinct pair from
  Level 0 — 3 terms total.
- **Level 2:** add `a/(a/b)` and `b/(a/b)`, the two new unordered
  distinct pairs involving a Level-1 term — 5 terms total.

The five Level-≤2 terms split `3 + 2`:

```
A-type (Levels 0+1): {a, b, a/b}        — 3 terms
B-type (Level  2):   {a/(a/b), b/(a/b)} — 2 terms
```

The (3, 2) partition used in §6 emerges from the axiom alone at
Level 2, without invoking the "alive" postulate of §5.5.

(Lean: `E213.Firmware.Raw.level1_card`,
`E213.Firmware.Raw.level2_new_card`,
`E213.Firmware.Raw.level2_total_card` — the 5 terms are
formalised as an explicit list with `List.Nodup` verified by
`decide`.)

---

## 2. Swap automorphism

**Definition 2.1 (Swap).** The map `swap : Raw → Raw` exchanges
the two base tokens and extends through `slash` by structural
recursion:

```
  swap a           := b
  swap b           := a
  swap (slash x y) := slash (swap x) (swap y).
```

At the canonical-form level (§1.2), swapping children of a
`slash` node may violate the ordering invariant; the Lean
implementation re-canonicalises after the swap. The
re-canonicalisation is an implementation artifact of the
canonical-form emulation and has no semantic content beyond
preserving `t.canonical = true`.

(Lean: `E213.Firmware.Raw.swap`.)

**Theorem 2.2 (Involution).** `swap (swap x) = x` for all
`x : Raw`.

*Proof.* By induction on `x`. Base cases `a, b`: direct from
`swap_a`, `swap_b`. Step: `swap (swap (x/y)) = swap (slash
(swap x) (swap y)) = slash x y` by the induction hypotheses on
`x` and `y`. ∎ (Lean: `E213.Firmware.Raw.swap_swap`.)

**Corollary 2.3 (Bijectivity).** `swap : Raw → Raw` is a
bijection.  (Lean: `E213.Firmware.Raw.swap_injective`,
`E213.Firmware.Raw.swap_surjective`,
`E213.Firmware.Raw.swap_bijective`.)

**Definition 2.4 (Raw-automorphism).** A *Raw-automorphism* is a
bijection `φ : Raw → Raw` satisfying

```
  φ (slash x y h) = slash (φ x) (φ y) h'
```

(for some distinctness certificate `h'`) and
`(φ a, φ b) ∈ {(a, b), (b, a)}`. By induction on `Raw`, such `φ`
is uniquely determined by its action on the two base tokens.

**Theorem 2.5 (Automorphism group).** `Aut(Raw) ≅ ℤ/2`; its
nontrivial element is `swap`.

*Proof.* By Definition 2.4, an automorphism is fixed by a choice
of permutation of `{a, b}`. There are exactly two such choices
(identity and swap); both preserve `slash` by construction.
Composition matches composition of the underlying permutations,
giving `S_2 ≅ ℤ/2`. ∎

**Lean coverage.** `Raw.swap_swap` (involution), `Raw.swap_comp_swap`
(`swap ∘ swap = id`), and `Raw.swap_ne_id` (`swap ≠ id`) together
formalise the ℤ/2 structure on `{id, swap}`. The classification
"every Raw-automorphism is `id` or `swap`" of Thm 2.5 is proved
here at the prose level only.

---

## 3. Hypervisor: the Lens framework

**Definition 3.1 (Lens).** A `Lens` with codomain `α` is a
triple

```
  Lens α = (base_a : α, base_b : α, combine : α → α → α).
```

**Definition 3.2 (Catamorphism / view).** For `L : Lens α`,
`L.view : Raw → α` is defined recursively by

```
  L.view a         := L.base_a
  L.view b         := L.base_b
  L.view (slash x y h) := L.combine (L.view x) (L.view y).
```

In Lean, `L.view` is implemented as a thin wrapper around
`Raw.fold`, which in turn unfolds over the internal `Tree`. The
Hypervisor layer sees only `L.view`; it does not reference `Tree`.

**Definition 3.3 (Kernel equivalence).** For `L : Lens α`, define
`L.equiv x y := L.view x = L.view y`. This is reflexive,
symmetric, and transitive — the kernel equivalence of `L.view`.
The axiom's absent equality primitive is supplied here, Lens-by-
Lens.

**Definition 3.4 (Refinement).** `L` refines `M` (written
`L.refines M`) iff `∀ x y, L.equiv x y → M.equiv x y`, i.e.
`M.view` factors through `L.view`.

**Theorem 3.5 (Catamorphism compatibility — symmetric case).**
For `α`, `aα, bα : α`, and **symmetric** `c : α → α → α`, the
catamorphism `view` of the Lens `⟨aα, bα, c⟩` satisfies

```
  view a = aα,
  view b = bα,
  view (slash x y h) = c (view x) (view y).
```

For non-symmetric `c`, no such `view` exists, because
`slash x y h = slash y x h'` (§1.2) would force
`c (view x) (view y) = c (view y) (view x)`.

(Lean: `E213.Firmware.Raw.fold_a`, `E213.Firmware.Raw.fold_b`,
`E213.Firmware.Raw.fold_slash`.)

**Remark 3.6 (Lens-relative semantics).** At the firmware layer,
`slash x y` and `slash y x` are the same Raw term (§1.2's
canonical form); `slash x x` is not a Raw term at all
(anti-reflexivity). A Lens with commutative `combine` respects
this identification natively; a Lens with non-commutative
`combine` cannot arise from a homomorphism out of Raw.

---

## 4. Signature forcing (meta-analysis)

The axiom of §1 already specifies the signature `(Fin 2, binary)`
— "two objects", "relation between". §4 provides a
*meta-comparison*: **if** one additionally imports a pairwise-
distinctness constraint on relation arguments (which the axiom
itself does not supply) into a generalised signature family,
**then** `(2, 2)` is the minimal non-vacuous such signature. The
distinctness constraint is adopted in this section for comparison
only; our `Raw` (Definition 1.1) does not rely on it.

**Definition 4.1 (Generalised Raw).** For `N, k : ℕ`, define

```
inductive RawNk (N k : Nat)
  | object : Fin N → RawNk
  | rel    : (Fin k → RawNk) → RawNk,
```

with the Reachable predicate

```
  base : (i : Fin N) → ReachableNk (object i)
  step : (f : Fin k → RawNk) →
         (∀ i, ReachableNk (f i)) →
         (∀ i j, i ≠ j → f i ≠ f j) →
         ReachableNk (rel f).
```

(Definition 1.1 is the case `N = k = 2`.)

**Lemma 4.2 (Pigeonhole).** For `N < k`, there is no injection
`Fin k → Fin N`.

*Proof sketch.* Induction on `N`. (Lean:
`E213.OS.Pigeonhole.no_inj_lt`.) ∎

**Theorem 4.3 (Vacuousness).** In `RawNk N k` with `N < k`, every
`ReachableNk`-term is a base object.

*Proof.* Induction on the Reachable derivation. Step case: the
distinct arguments `f : Fin k → RawNk` lift to an injection
`Fin k → Fin N`, contradicting Lemma 4.2. (Lean:
`E213.OS.ArityForcingGeneral.reachable_base_only`.) ∎

**Corollary 4.4 (Minimal signature).** Non-vacuity requires
`N ≥ k`. The remaining arities `k = 0, 1` are degenerate:

- `k = 0`: `rel` takes no arguments, producing a single constant.
- `k = 1`: Reachable terms form a linear chain, with no branching.

Call an arity *non-degenerate* iff `k ≥ 2`. The minimal
non-degenerate, non-vacuous signature is therefore
`(N, k) = (2, 2)`.

This is the signature of Definition 1.1.

**Scope note.** Corollary 4.4 reads "forced" only inside the §4
distinctness hypothesis. The axiom of §1 independently fixes
`(Fin 2, binary)`; §4 is a sanity check that the choice
coincides with the minimal non-vacuous signature under an
additional stipulation, not an alternative derivation from the
axiom.

---

## 5. Atomicity

§5 derives the unique vertex count admitting a canonical atomic
partition. The arithmetic has three inputs, with distinct
axiomatic statuses:

- a **lower bound** on atom size (structural choice, §5.2);
- the **atom set** `A = {2, 3}` itself (arithmetic fact, §5.4);
- an **alive** predicate on multiplicities (postulate, §5.5).

Theorem 5.3 below ties the three together and concludes
`n = 5` uniquely. Theorem 5.7.2 (Pair Forcing) re-derives the
numerical rigidity without invoking the alive postulate.

### 5.1 Atomic: definitions

**Setup.** Given `A = {2, 3}`, consider decompositions of
`n ∈ ℕ` as `n = 2a + 3b` with `(a, b) ∈ ℕ²`.

**Definition 5.1 (Alive).** A decomposition `(a, b)` is *alive*
iff `a` and `b` are both odd.

**Definition 5.2 (Atomic).** `n` is *atomic* iff there exists a
unique pair `(a, b) ∈ ℕ²` with `n = 2a + 3b`, and that pair is
alive.

**Theorem 5.3 (Atomicity).** `n ∈ ℕ` is atomic iff `n = 5`.

*Proof.* (Lean: `E213.OS.Atomicity.atomic_iff_five`.)

*`⇐` (Existence at `n = 5`).* From `3b ≤ 5` we get `b ∈ {0, 1}`;
`b = 0` gives `2a = 5`, impossible; `b = 1` gives `a = 1`. The
unique decomposition is `(1, 1)`, alive. Hence `5` is atomic.

*`⇒` (Only `n = 5`).* Let `(a, b)` be the unique alive
decomposition of `n`. The *Bézout shift*
`(a, b) ↦ (a ± 3, b ∓ 2)` preserves `2a + 3b`. If `a ≥ 3`, then
`(a - 3, b + 2) ∈ ℕ²` is a valid second decomposition,
contradicting uniqueness; hence `a < 3`. If `b ≥ 2`, then
`(a + 3, b - 2) ∈ ℕ²` is likewise a second decomposition; hence
`b < 2`. Combined with `a, b` odd nonnegative, this forces
`a = b = 1`, giving `n = 5`. ∎

**Corollary 5.4 (Canonical partition).** The unique atomic `n`
admits the unique alive decomposition `(1, 1)`: one 2-block and
one 3-block, `5` vertices split as
`V = V_A ⊔ V_B, |V_A| = 3, |V_B| = 2`.

### 5.2 Characterisation of the atom set

**Proposition 5.5 (Characterisation of `{2, 3}`).** An integer
`n ≥ 2` cannot be written as `n = n_1 + ⋯ + n_k` with `k ≥ 2` and
each `n_i ≥ 2` iff `n ∈ {2, 3}`.

*Proof.* (Lean: `E213.OS.NonDecomposable.non_decomposable_iff`.)

A `k`-part decomposition `(k ≥ 2, \text{parts} ≥ 2)` collapses to
a 2-part one: `a := n_1, b := n_2 + ⋯ + n_k`; then `a ≥ 2` and
`b ≥ 2(k-1) ≥ 2`. Case analysis:

- `n ∈ {2, 3}`: `a + b ≥ 4 > n`. Non-decomposable.
- `n = 4`: `2 + 2`. Decomposable.
- `n ≥ 5`: `2 + (n - 2)`, `n - 2 ≥ 3 ≥ 2`. Decomposable. ∎

We henceforth call `n` *non-decomposable* iff `n ∈ {2, 3}`.


### 5.3 Status of the atom hypothesis

Theorem 5.3 rests on three ingredients. We audit each.

**(a) Lower bound `n ≥ 2`.** *Structural choice.* An "atom" is a
Raw-subtree used as a partition block; its size is its leaves
count. A bare base token (`a` or `b`) has leaves `1` and does not
exercise the `slash` constructor at all. Excluding such atoms
asks every partition block to involve at least one `slash`
application, i.e. leaves `≥ 2`. The choice is made to keep the
partition analysis non-degenerate; it is not forced by the axiom.

**(b) Atom set `A = {2, 3}`.** *Arithmetic derivation.* By
Proposition 5.5, the non-decomposable integers `≥ 2` are exactly
`{2, 3}`. This is independent of §§1–4 and is the fully
Raw-intrinsic component of the atom hypothesis.

*Primitive-data parallel.* The same two sizes occur as the base
pair `|{a, b}| = 2` and the first closure `|{a, b, a/b}| = 3`.
(Lean: `E213.OS.PrimitiveSizes.primitive_sizes_eq_nondecomposable`.)
This is noted for intuition; the arithmetic of Proposition 5.5 is
what fixes `A`.

**(c) Alive = both-odd.** *Postulate.* The condition "paired
copies of a structurally identical atom annihilate, leaving
multiplicity `mod 2`" is adjoined to §5 as an independent
structural principle. The axiom of §1 does not supply it as a
theorem. The motivation is the exterior-algebra pattern
`v ∧ v = 0`, the standard realisation of antisymmetric
multiplicity. The formal content in Lean is a definitional
equivalence (`E213.OS.Alive.alive_iff_odd_pair`); the
*justification* from Raw is the postulate recorded here.

**Alternative route (§1.3).** The (3, 2) vertex-count partition
is derivable *directly* from the firmware at Level 2 (§1.3),
without invoking the alive postulate. Theorem 5.3 is then a
separate arithmetic confirmation that `n = 5` is the unique
atomic count. Readers sceptical of the alive postulate may take
§1.3 + §6 as the primary route and treat §5 as arithmetic
corroboration.


### 5.4 Pair Forcing Theorem

Proposition 5.5 fixes the atom set `{2, 3}` given that atoms form
a coprime pair. A sharper question: among *all* coprime pairs
`(p, q)` with `2 ≤ p < q`, which admit a unique atomic vertex
count (in the sense of Definition 5.2 generalised from `2, 3` to
`p, q`)?

**Definition 5.7 (count).** For `p, q ≥ 2`,
```
  count(p, q) := ⌊p/2⌋ · ⌊q/2⌋.
```

*Combinatorial interpretation (motivation).* `⌊q/2⌋` is the
number of odd positive integers less than `q`, and `⌊p/2⌋` the
number less than `p`. Under the Bézout uniqueness bound
`a < q ∧ b < p`, the count of odd-positive pairs `(a, b)` with
`pa + qb = n` unique is `⌊p/2⌋ · ⌊q/2⌋`. We do not formalise the
equality "count of atomic `n`s = `⌊p/2⌋ · ⌊q/2⌋`" for general
`(p, q)` in Lean; Theorem 5.8 is stated purely as the arithmetic
identity below.

**Theorem 5.8 (Pair Forcing).** For coprime `p, q` with
`2 ≤ p < q`,
```
  count(p, q) = 1  ⟺  (p, q) = (2, 3).
```

*Proof.* Both `⌊p/2⌋ ≥ 1` and `⌊q/2⌋ ≥ 1` (from `p, q ≥ 2`);
their product equals `1` iff both equal `1`. Now
`⌊k/2⌋ = 1 ⟺ k ∈ {2, 3}`. Combined with `p < q` and coprimality,
the unique solution is `(p, q) = (2, 3)`. ∎ (Lean:
`E213.OS.PairForcing.count_eq_one_iff`.)

**Corollary 5.9 (Narrative consolidation).** The arithmetic
atom-pair `(2, 3)` — the values stipulated separately in §4
(atom set size 2, under a minimality choice) and §5.5 (atom
values, by non-decomposability) — coincides with the unique
coprime pair `(p, q)` with `2 ≤ p < q` and `count(p, q) = 1`.
Pair Forcing does *not* by itself replace §4 or §5.5 (each uses
distinct hypotheses); the three arguments converge on the same
pair.

**Remark 5.10 (Rigidity).** The pair structure is narrow:

- Three or more atoms (`|A| ≥ 3`) yield no atomic `n`: Bézout
  shifts proliferate and always break uniqueness
  (`foundations/experiments/FND_042`).
- Non-coprime atoms restrict `n` to multiples of `gcd`, losing
  the universal count theorem.
- Weakening the alive condition contradicts the antisymmetric-
  multiplicity postulate (§5.3(c)).

Thus `(p, q, n) = (2, 3, 5)` is an arithmetic fixed point of the
atomicity framework.

---

## 6. Block structure and invariance

**Origin of the partition.** §1.3 derived, from the axiom alone,
the Level-2 closure `{a, b, a/b, a/(a/b), b/(a/b)}` with a
natural split of `3 + 2` Raw terms. §5.4 independently concludes
that `n = 5` with `(|V_A|, |V_B|) = (3, 2)` is the unique atomic
vertex count. §6 treats the partition abstractly as
`V := V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2`, independent of the
realisation.

Take `V := Fin 5`, `V_A := {0, 1, 2}`, `V_B := {3, 4}`.

**Definition 6.1.** The partition indicator is
`isA : Fin 5 → Bool`, `isA i := (i.val < 3)`.

**Definition 6.2 (Block-pair classifier).** Define
`classify : Fin 5 × Fin 5 → BlockPair`, where `BlockPair` has
six values:

```
AAdiag   (i, i), i ∈ V_A       (3 pairs)
AAoff    (i, j), i ≠ j ∈ V_A   (6 pairs)
AB       (i, j), i ∈ V_A, j ∈ V_B  (6 pairs)
BA       (i, j), i ∈ V_B, j ∈ V_A  (6 pairs)
BBdiag   (i, i), i ∈ V_B       (2 pairs)
BBoff    (i, j), i ≠ j ∈ V_B   (2 pairs)
```

The six orbits exhaust `Fin 5 × Fin 5`:
`3 + 6 + 6 + 6 + 2 + 2 = 25 = |V|²`.

**Definition 6.3 (Partition-preserving permutation).** A bijection
`σ : Fin 5 → Fin 5` *preserves the partition* iff
`isA (σ i) = isA i` for all `i`.

The group of such bijections is `S_{V_A} × S_{V_B} ≅ S_3 × S_2`,
of order 12.

**Definition 6.4 (Block-constant weight).** A function
`W : Fin 5 × Fin 5 → α` is *block-constant* iff it factors through
`classify`: `W i j = f (classify i j)` for some
`f : BlockPair → α`.

**Theorem 6.5 (Block-constancy ⟹ invariance).** If `W` is
block-constant, then `W` is invariant under every partition-
preserving bijection: `W (σ i) (σ j) = W i j` for every such `σ`
and all `i, j`.

*Proof.* For bijective partition-preserving `σ`,
`isA (σ i) = isA i` and `σ i = σ j ↔ i = j`, so
`classify (σ i) (σ j) = classify i j`. Since `W = f ∘ classify`,
the claim follows. ∎ (Lean:
`E213.App.Simplex.block_constant_implies_aut_invariant`.)

**Theorem 6.6 (Invariance ⟹ block-constancy).** Conversely, if
`W` is invariant under every partition-preserving bijection, then
`W` is block-constant.

*Proof (prose only; not formalised in Lean).* It suffices to show
two pairs in the same `classify`-class have equal `W`-values. Any
`σ ∈ S_3` on `V_A` extends to a partition-preserving bijection
`σ̂` of `V` by fixing `V_B`, and similarly for `τ ∈ S_2` on
`V_B`. The six classes are handled by the transitive actions of
`S_3` on ordered distinct pairs of `V_A` (`|ordered| = 6 = |S_3|`)
and of `S_2` on ordered distinct pairs of `V_B` (`|ordered| = 2 =
|S_2|`), together with the diagonals handled by transitivity of
each factor on its domain. ∎

---

## 7. Aut-faithful Lens existence (ℂ-uniqueness)

When does the structure of §§1–6 admit a Lens whose automorphism
behaviour matches that of `Raw` itself? The class of candidate
codomains is specified by conditions (C1)–(C4) below; the
existence and uniqueness of a satisfying codomain are then
derived. The identification of the codomain with `ℂ` is recorded
only after the derivation.

### 7.1 The class 𝒞

We seek `K` an `ℝ`-algebra satisfying:

- **(C1) Finite-dimensional over `ℝ`.** *Stipulation.* Lens values
  are determined inductively from two base values and one binary
  operation; an infinite-dimensional codomain carries strictly
  more information (in the sense of `dim_ℝ K`) than the axiom's
  two-generator / binary-operation scale provides.
  Infinite-dimensional ℝ-algebras with `Aut_ℝ = ℤ/2` could in
  principle exist; they are excluded here as extraneous.
- **(C2) Commutative.** *Structural reflection of §1.1's
  "between".* The Raw canonical form identifies `slash x y` with
  `slash y x`; commutativity of `combine` at the Lens layer is
  the precise value-level translation. Dropping (C2) admits `ℍ`
  (Cor 7.6), which the axiom's symmetric reading rejects via Aut
  mismatch; so (C2) is not merely natural but *enforced* by
  Aut-faithfulness.
- **(C3) Unital.** *Stipulation.* A multiplicative identity is
  adopted to enable the field-classification step of Theorem 7.4.
  Non-unital ℝ-algebras could in principle satisfy the other
  conditions; they are excluded for classification-theoretic
  convenience.
- **(C4) Division algebra.** *Structural reflection of
  non-degeneracy.* Every nonzero element invertible: a Lens value
  cannot vanish without the corresponding Raw term being absent.
  Without (C4), `ℝ ⊕ ℝ` (coordinate-wise multiplication)
  satisfies the remaining conditions and has
  `|Aut_ℝ(ℝ ⊕ ℝ)| = 2` (coordinate swap), which would falsely
  match `Aut(Raw)`. (C4) excludes this false competitor.

Call this class `𝒞`.

**Status of (C1)–(C4).** Only (C2) is forced by Aut-faithfulness
(Corollary 7.6). (C1), (C3), (C4) are acknowledged stipulations
chosen for the classification theorem to apply. "Uniqueness of
`ℂ`" is uniqueness *within* `𝒞`, not uniqueness among all
ℝ-algebras.

### 7.2 Faithful codomain

**Definition 7.1 (Algebra automorphism).** For `K ∈ 𝒞`,
`Aut_ℝ(K)` denotes the group of `ℝ`-algebra automorphisms (ring
automorphisms fixing `ℝ ⊆ K` pointwise).

**Definition 7.2 (Aut-equivariance).** A Lens `L` with codomain
`K ∈ 𝒞` is *Aut-equivariant* iff there is a group homomorphism
`ρ : Aut(Raw) → Aut_ℝ(K)` such that
`L.view (τ x) = ρ(τ) (L.view x)` for all `τ ∈ Aut(Raw)` and
`x : Raw`.

**Definition 7.3 (Aut-faithfulness).** `L` is *Aut-faithful* iff
the induced `ρ` is a group *isomorphism*
`Aut(Raw) ≅ Aut_ℝ(K)`.

**Theorem 7.4 (Existence and uniqueness in `𝒞`).** Within `𝒞`:

1. *(Classification.)* Up to `ℝ`-algebra isomorphism, `𝒞` has
   exactly two elements: a one-dimensional `K_1` and a
   two-dimensional `K_2`.
2. *(Aut groups.)* `|Aut_ℝ(K_1)| = 1`, `|Aut_ℝ(K_2)| = 2`.
3. *(Faithful codomain.)* Combined with `Aut(Raw) ≅ ℤ/2`
   (Theorem 2.5), exactly `K_2` admits an Aut-faithful Lens.

*Proof (prose; not formalised in Lean).*

(1) Every `K ∈ 𝒞` is a finite field extension of `ℝ` (by
(C2)+(C3)+(C4) + (C1)). Irreducible polynomials over `ℝ` have
degree `1` or `2`, so `[K : ℝ] ∈ {1, 2}`. One isomorphism class
at each dimension.

(2) For `K_1`, any `ℝ`-algebra endomorphism fixes `1`, hence
`K_1`; `Aut_ℝ(K_1) = {id}`. For `K_2 = ℝ[α]` with `α² = -1`, any
`σ` is determined by `σ(α)`, and `σ(α)² = σ(α²) = -1` gives
`σ(α) = ±α`; `|Aut_ℝ(K_2)| = 2`.

(3) Aut-faithfulness requires `|Aut(Raw)| = |Aut_ℝ(K)| = 2`;
(2) matches only `K_2`, where `ρ` lifts `swap` to the nontrivial
element. ∎

**Corollary 7.5 (Identification with ℂ).** `K_2` is, by direct
construction, the complex numbers. Adjoining a root of `x² + 1`
to `ℝ` gives the standard presentation `ℝ[i]`. The nontrivial
element of `Aut_ℝ(K_2)` is complex conjugation `i ↦ -i`. The
unique Aut-faithful codomain in `𝒞` is the field `ℂ`, with
`swap` lifted to conjugation.

**Corollary 7.6 (ℍ excluded).** Dropping (C2) admits the
quaternions `ℍ` (finite-dim unital division ℝ-algebra).
`Aut_ℝ(ℍ) ≅ SO(3)` is a Lie group of dimension 3, so
`|Aut_ℝ(ℍ)| ≠ |Aut(Raw)| = 2`. No Aut-faithful Lens over `ℍ`
exists. (C2) is therefore the decisive constraint separating
`K_2` from `ℍ`.

**Remark 7.7 (Relation to Hurwitz–Frobenius).** Frobenius's
theorem (finite-dim associative ℝ-division algebras are `ℝ`, `ℂ`,
`ℍ`) and Hurwitz's (`ℝ`-composition algebras are
`ℝ, ℂ, ℍ, 𝕆`) play no external role here. Step (1) of Theorem
7.4 uses only the commutative fragment of Frobenius, which
reduces to the elementary classification of finite `ℝ`-field
extensions.

---

## Conclusion

The minimal system defined by the 3-clause axiom consists of the
following structure. For each item we mark the Lean status:
**[✓]** fully formalised; **[partial]** some underlying theorems
formalised, full statement informal; **[prose]** informal only.

**From the axiom (§§1–3):**

1. **[✓]** `Raw`, a free commutative magma on two generators with
   no fixed points, emulated in Lean 4 core as the canonical-form
   subtype of a free ordered magma (Def 1.1). No equality or
   apartness primitive is part of the axiom; the Lean encoding
   uses Lean's propositional equality as external bookkeeping.

2. **[partial]** A single nontrivial Raw-automorphism, the swap
   involution. Formalised: `Raw.swap`, `Raw.swap_swap`,
   `Raw.swap_comp_swap`, `Raw.swap_ne_id` — together giving the
   ℤ/2 structure on `{id, swap}`. The full classification Thm 2.5
   ("every Raw-aut is `id` or `swap`") is proved at the prose
   level.

3. **[✓]** The Lens / catamorphism framework (§3). Any symmetric
   `combine` determines a unique `view : Raw → α` via
   `Raw.fold`. Equality on `Raw` becomes available as a Lens
   kernel; apartness is Lens-dependent.

**Meta-analysis (§4):**

4. **[✓, under an imported distinctness constraint]** The
   generalised signature family `RawNk` with pairwise-distinct
   relation arguments: `(N, k) = (2, 2)` is the minimal
   non-degenerate non-vacuous signature (Thm 4.3, Cor 4.4). The
   axiom itself fixes `(Fin 2, binary)` directly; §4 is a
   sanity-check convergence, not an alternative derivation.

**From the axiom + alive postulate (§§5–6):**

5. **[✓]** Atom set `{2, 3}` (Prop 5.5) + lower bound `≥ 2`
   (structural choice, §5.3(a)) + alive postulate (§5.3(c))
   together yield `n = 5` as the unique atomic vertex count
   (Thm 5.3), giving the canonical `|V_A|, |V_B| = 3, 2`
   partition.

5'. **[✓]** Pair Forcing (Thm 5.8): among all coprime pairs
   `(p, q)` with `2 ≤ p < q`, `count(p, q) = 1` iff
   `(p, q) = (2, 3)`. Does not by itself replace §4 or §5.5; the
   three arguments converge.

6. **[partial]** `S_3 × S_2`-invariance on `V × V` is equivalent
   to block-constancy (Thms 6.5–6.6). Lean formalises the
   forward direction (6.5); the converse (6.6) is prose only.

**Within the class 𝒞 (§7):**

7. **[prose]** `𝒞`-uniqueness of `ℂ` (Thm 7.4, Cor 7.5). No
   Lean formalisation.

---

**Honest summary.** The axiom forces: the free commutative magma
on 2 generators with no fixed points (§1), its catamorphism / Lens
framework (§3), and the arithmetic fixed point `(p, q, n) =
(2, 3, 5)` under the coprime-pair count = 1 condition (§5.4).

The following are acknowledged stipulations beyond the axiom:

- atom lower bound `≥ 2` (§5.3(a));
- alive = both-odd postulate (§5.3(c));
- class-`𝒞` conditions (C1), (C3), (C4) of §7.1 — only (C2) is
  enforced by Aut-faithfulness.

`Aut(Raw) ≅ ℤ/2` (Thm 2.5) and the `ℂ`-identification (Thm 7.4)
are proved at the prose level; their full Lean formalisations are
partial or absent.

This is the minimal system defined by the 3-clause axiom.

End.
