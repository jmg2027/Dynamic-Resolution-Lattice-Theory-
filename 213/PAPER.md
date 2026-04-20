# The Minimal System of Binary Relations

**Axiom.**

1. *Something exists.*
2. *To know what it is, another something is required.*
3. *That other something is also a something.*

Clauses (1)–(2) name an existing "something" and a distinguishing
partner; (3) closes the rule recursively. We take this as the sole
axiom. Clauses (1) + (3) give at least two somethings; clause (2)
is the primitive *distinction*, applied recursively.

We separate the treatment into two layers:

- **Firmware (§1).** The raw type `Raw` and its three constructors,
  implementing the three axiom clauses as a free inductive type.
  No equality, inequality, ordering, or subtree-identification is
  available at this layer.
- **Hypervisor (§4 and beyond).** Each `Lens L : Raw → α` carries
  a codomain with its own notion of equality; `L.equiv x y :=
  L.view x = L.view y` is the kernel-equivalence. "Same/different"
  on Raw is thus Lens-relative.

---

## 0. Notation and conventions

- `Fin n` denotes the standard `n`-element type `{0, 1, …, n-1}`.
- `inductive T` denotes an initial algebra presentation: `T` is the
  smallest type closed under the listed constructors.
- All claims below are formally checked in Lean 4 (`E213.*`
  modules, 0 `sorry`); we cite the Lean name where relevant.
- The axiom does *not* supply an equality or inequality primitive
  on Raw. Lean's propositional equality is external bookkeeping,
  used only for case analysis (which inductive constructor a term
  begins with). Apartness is not part of Raw; any appeal to it
  belongs to a Lens.

---

## 1. Firmware: the primitive type

### 1.1 Target structure

The axiom's clauses (1)–(3) together specify:
- two initial "somethings" `a, b`;
- a binary *distinction* operator `slash` that takes two (necessarily
  distinct, by clause (2)) somethings and produces a new something;
- recursion (clause (3)): the output of `slash` is again a
  something, so `slash` applies to it in turn.

Reading "another" (clause 2) and "between" (clause 2–3) semantically:
- **Anti-reflexive:** `slash x x` is *not* a valid term; distinguishing
  `x` from `x` reveals nothing.
- **Symmetric:** `slash x y = slash y x`; "between" is directionless.

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
orders the children so the result is canonical; the associated
theorem `Raw.slash_comm (h : x ≠ y) : Raw.slash x y h = Raw.slash
y x (Ne.symm h)` certifies that both input orderings collapse to
the same Raw term — the symmetric reading of the axiom.

(Lean: `E213.Firmware.Raw.slash`, `E213.Firmware.Raw.slash_comm`.)

### 1.3 The first three levels

Let the *depth* of a Raw term be its tree depth. The closure by
levels is:

- **Level 0**: `{a, b}` — 2 terms.
- **Level 1**: add `a/b` (the sole unordered distinct pair from
  Level 0) — 3 terms.
- **Level 2**: add `a/(a/b)` and `b/(a/b)` (the two new unordered
  distinct pairs involving a Level-1 term) — 5 terms.

```
A-type (Levels 0+1): {a, b, a/b}        — 3 terms
B-type (Level  2):   {a/(a/b), b/(a/b)} — 2 terms
```

The (3, 2) partition of §7 emerges from the axiom alone at Level 2,
without invoking the alive postulate of §6.6(c). See Remark 7.0.
(Lean: `E213.Firmware.Raw.level1_card`,
`E213.Firmware.Raw.level2_new_card`,
`E213.Firmware.Raw.level2_total_card` —
the 5 terms at depth ≤ 2 are formalised as an explicit list with
`Nodup` verified by `decide`.)

**Definition 1.2 (Depth).** A structural-recursive height measure:

```
Raw.depth : Raw → Nat
  | a         => 0
  | b         => 0
  | slash x y => 1 + max x.depth y.depth.
```

A function on Raw, not a predicate; uses no equality.

---

## 2. (Removed.)

The former §2 contained `Reachable ↔ wellFormed` and related
machinery that presupposed an apartness primitive `x ≠ y` at the
level of Raw. The present formulation places the anti-reflexive
and symmetric readings of the axiom *inside* the Raw type itself
(via the canonical-form subtype of §1.2): `slash x x` is
excluded by `Tree.cmp x x = .eq ≠ .lt`, and the smart constructor
`Raw.slash` takes an explicit `h : x ≠ y` hypothesis. The
previous "Reachable" predicate is therefore redundant — being a
Raw term already implies "reachable" and "well-formed" under the
new encoding.

Section numbers §3–§8 are retained; internal cross-references
formerly pointing to §2 are now pointers to §1 or to the Lens
layer (§4), as appropriate.

---

## 3. The swap automorphism

**Definition 3.1 (Swap).** Define `swap : Raw → Raw` by

```
  swap a         := b
  swap b         := a
  swap (slash x y) := slash (swap x) (swap y).
```

The rule simply exchanges the two base tokens and extends through
`slash` by structural recursion. At the canonical-form level
(§1.2), swapping children of a `slash` node may violate the
ordering invariant, so the Lean implementation re-canonicalizes
(re-orders children) after the swap. The re-canonicalization is
an implementation artifact of the canonical-form emulation and
has no semantic content beyond preserving `t.canonical = true`.
(Lean: `E213.Firmware.Raw.swap`, `E213.Firmware.Raw.swap_a`,
`E213.Firmware.Raw.swap_b`, `E213.Firmware.Raw.swap_swap`.)

**Theorem 3.2 (Involution).** `swap (swap x) = x` for all `x : Raw`.

*Proof.* By induction on `x`. Base cases `a, b`: direct. Step:
`swap (swap (x/y)) = swap (swap x / swap y) = swap (swap x) / swap
(swap y) = x/y` by IH. ∎

**Corollary 3.3 (Bijectivity).** `swap` is a bijection on `Raw`.
(Lean: `E213.Firmware.Raw.swap_injective`,
`E213.Firmware.Raw.swap_surjective`, `E213.Firmware.Raw.swap_bijective`.)

**Definition 3.4 (Raw-automorphism).** A *Raw-automorphism* is a
bijection `φ : Raw → Raw` satisfying

```
  φ (slash x y) = slash (φ x) (φ y)
```

and either `(φ a = a ∧ φ b = b)` or `(φ a = b ∧ φ b = a)`. Such
`φ` is uniquely determined by its action on the two base tokens;
the recursive clause then fixes `φ` on every `slash` term.

**Theorem 3.5 (Automorphism group).** `Aut(Raw) ≅ ℤ/2`. Its
nontrivial element is `swap`.

*Proof.* (Lean formalization partial: `Raw.swap_swap` establishes
the involution, `Raw.swap_comp_swap` the composition identity
`swap ∘ swap = id`, and `Raw.swap_ne_id` establishes nontriviality
— so `{id, swap}` under composition is the ℤ/2 group. The full
classification statement "all Raw-automorphisms are id or swap"
is proved here at the prose level only.)
By Definition 3.4, an automorphism is determined by a choice of
permutation of `{a, b}`. There are two such choices:
identity and swap. Both preserve `slash` by construction.
Composition matches composition of the underlying permutations
of `{a, b}`, which is `S_2 ≅ ℤ/2`. ∎

---

## 4. Hypervisor: the Lens framework

**Definition 4.1 (Lens).** A `Lens` with codomain type `α` is a
triple

```
  Lens α = (base_a : α, base_b : α, combine : α → α → α).
```

**Definition 4.2 (Catamorphism).** The `view` of a Lens
`L : Lens α` is

```
  L.view a         := L.base_a
  L.view b         := L.base_b
  L.view (slash x y) := L.combine (L.view x) (L.view y).
```

**Definition 4.3 (Kernel equivalence).** For `L : Lens α`, define
`L.equiv x y := L.view x = L.view y`. This is reflexive, symmetric,
and transitive; it is the kernel equivalence of `L.view`. The
axiom's absent equality primitive is supplied here, Lens-by-Lens.

**Definition 4.4 (Refinement).** `L` refines `M` (written
`L.refines M`) iff `∀ x y, L.equiv x y → M.equiv x y`, i.e.
`M.view` factors through `L.view`.

**Theorem 4.5 (Catamorphism universality, symmetric case).** For any
`α`, `aα, bα : α`, and **symmetric** `c : α → α → α` (i.e.
`∀ u v, c u v = c v u`), the catamorphism `view` of the Lens
`⟨aα, bα, c⟩` satisfies `view a = aα`, `view b = bα`, and
`view (slash x y h) = c (view x) (view y)` for all distinct `x, y`.
Uniqueness (that any homomorphism with these equations equals
`view`) holds by induction on `Raw`.

*Proof.* Existence by the inductive definition of `Raw.fold`;
equality on `slash` needs symmetry of `c` because `Raw.slash`
canonicalizes child order (§1.2). For the non-symmetric case, no
such `φ` exists because the two homomorphism equations force
commutativity. (Lean: `E213.Firmware.Raw.fold_a`,
`E213.Firmware.Raw.fold_b`, `E213.Firmware.Raw.fold_slash`.) ∎

**Remark (symmetry, self-distinction, and the Lens).** The axiom
does not distinguish "the pair (x, y)" from "the pair (y, x)": any
such distinction would require an ordering primitive the axiom
lacks. At the firmware layer `slash x y` and `slash y x` are
distinct Raw terms (distinct inductive constructor applications),
but this distinctness carries no semantic weight. A Lens with
*commutative* `combine` quotients them, recovering symmetric
"between." Similarly, `slash x x` is a Raw term whose image is
`L.combine (L.view x) (L.view x)`; whether that is trivial,
zero, idempotent, or something else is entirely the Lens's
responsibility.

---

## 5. Signature forcing (meta-analysis under a distinctness constraint)

The axiom of §1 already fixes the signature as `(Fin 2, binary)`
("two objects", "relation between"). This section provides a
*meta-comparison*: if we *additionally* require the relation
constructor to take pairwise-distinct arguments (a distinctness
constraint that the axiom itself does not supply), then `(2, 2)`
is the minimal non-vacuous such signature. The constraint is
adopted here for comparison only; our Raw (Definition 1.1) has
no such constraint.

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

*Proof.* (Lean: `E213.OS.Pigeonhole.no_inj_lt`.) It suffices to show
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

*Proof.* (Lean: `E213.OS.Atomicity.atomic_iff_five`.)

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

*Proof.* (Lean: `E213.OS.NonDecomposable.non_decomposable_iff`.)

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

(a) *Lower bound `n ≥ 2`.* "Atom" here means a Raw-subtree used as
a partition block; its size is its leaves count. A bare base token
(`a` or `b`) has leaves `1` and does not exercise the `slash`
constructor at all. Excluding such atoms amounts to asking that
every partition block involves at least one `slash` application,
i.e. leaves `≥ 2`. This is a structural choice, not an axiomatic
consequence: a self-distinction `x/x` has leaves `2` and is a
Raw term under the present axiom. The choice is made to keep the
partition analysis non-degenerate.

(b) *Atom identification `A = {2, 3}`.* The principled derivation
is arithmetic. By Proposition 6.5, the non-decomposable integers
`≥ 2` — those that cannot be written as a sum of `k ≥ 2` parts
each `≥ 2` — are exactly `{2, 3}`. This is the standard meaning of
"atom" (irreducible under the composition in question) and it is
independent of §1–5. Combined with (a), the atom set is fixed as
`A = {2, 3}`.
(Lean: `E213.OS.NonDecomposable.non_decomposable_iff`.)

An informal parallel: the same two sizes occur as natural
cardinalities in the primitive data — the base pair (`|{a, b}| =
2`) and the first closure under a single `slash` application
(`|{a, b, a/b}| = 3`). This observation is consistent with
Proposition 6.5 but is not used to derive it; it is recorded for
intuition.
(Lean: `E213.OS.PrimitiveSizes.primitive_sizes_eq_nondecomposable`.)

(c) *The alive predicate is a structural principle — used here as
an independent confirmation, not the sole route.* The condition
"both `a` and `b` odd" states that pairs of structurally identical
atom-copies annihilate, leaving the multiplicity `a mod 2`. The
axiom of §1 supplies Raw and its constructors; it does *not*
supply such a pair-cancellation rule as a theorem. We retain the
alive condition as a postulate in this section's arithmetic.

**Note (route via §1.3 avoids the postulate).** The (3, 2)
vertex-count partition is *already* derived in §1.3 from the
Level-2 closure of the free-commutative-magma-without-fixed-points.
That route does not use the alive postulate at all. The Level-2
closure gives 5 Raw terms split 3+2; Theorem 6.3 then *confirms*
the arithmetic uniqueness of `n = 5` from a different direction.
Readers who regard the alive postulate as philosophically
suspicious may drop §6 entirely and rely on §1.3 + §7.

(The former versions of this paper attempted to derive the alive
predicate from a "Raw distinctness rule `x ≠ y`". The present
axiom contains no such rule (§1): apartness is not a Raw
primitive, and appeals to it at the multiplicity level are not
valid. We accordingly mark this step as a postulate.)

The formal content of (c) is the equivalence
`alive(a, b) ⟺ a % 2 = 1 ∧ b % 2 = 1` (a definitional
rephrasing, Lean: `E213.OS.Alive.alive_iff_odd_pair`);
the *motivation* is the exterior-algebra pattern `v ∧ v = 0`,
which is the standard concrete realization of antisymmetric
multiplicity.

**Scope claim (honest).**

- (a) *Lower bound `≥ 2`*: a structural choice to exclude the
  degenerate "bare object" atoms; no appeal to `≠` is made.
- (b) *Atom set `{2, 3}`*: derived from the axiom via Proposition
  6.5 (non-decomposable integers ≥ 2) and sharpened by §6.7
  (Pair Forcing) — this is the one fully Raw-intrinsic component.
- (c) *Alive predicate*: postulated as an antisymmetric-multiplicity
  principle; not derivable from the axiom alone.

Theorem 6.3 therefore depends on (c) as an additional structural
principle beyond the axiom. The arithmetic sharpening (§6.7)
isolates the numerical rigidity independently of (c).

Theorem 6.3 (Atomicity → `n = 5`) follows from the axiom *together
with* the antisymmetric-multiplicity principle (c). The arithmetic
sharpening §6.7 relies only on the axiom's numerical structure;
(c) is isolated to the "alive" clause of Definition 6.2.

### 6.7 Pair Forcing Theorem (unification of §5 and §6)

Proposition 6.5 fixes the atom set to `{2, 3}` *given* that atoms
form a coprime pair. A sharper question is: among *all* coprime
pairs `(p, q)` with `2 ≤ p < q`, which admit a unique atomic
vertex count?

**Definition 6.7.1.** For `p, q ≥ 2`, define
```
  count(p, q) := ⌊p/2⌋ · ⌊q/2⌋.
```

**Combinatorial interpretation (motivation, not a theorem).**
The integer `⌊q/2⌋` is the number of odd positive integers less
than `q`, and `⌊p/2⌋` the number less than `p`. Under the Bézout
uniqueness bound `a < q ∧ b < p`, the count of odd-positive pairs
`(a, b)` is therefore `⌊p/2⌋ · ⌊q/2⌋`. We do not formalise the
equality "count of atomic `n`'s = `⌊p/2⌋ · ⌊q/2⌋`" for general
`(p, q)` in Lean; it is not needed for Theorem 6.7.2, which is
stated purely as the arithmetic identity below.

**Theorem 6.7.2 (Pair Forcing).** For coprime `p, q` with
`2 ≤ p < q`,
```
  count(p, q) = 1  ⟺  (p, q) = (2, 3).
```
*Proof.* Both `⌊p/2⌋ ≥ 1` and `⌊q/2⌋ ≥ 1` (from `p, q ≥ 2`). Their
product equals `1` iff both equal `1`. Now `⌊k/2⌋ = 1 ⟺ k ∈ {2, 3}`.
Combined with `p < q` and coprimality, the unique solution is
`(p, q) = (2, 3)`. ∎ (Lean: `E213.OS.PairForcing.count_eq_one_iff`.)

**Corollary 6.7.3 (Narrative consolidation).** The arithmetic
atom-pair `(2, 3)` — the values stipulated separately in §5
(atom set size 2, by Pigeonhole plus choice of minimality) and
§6.5 (atom values, by non-decomposability) — coincides with the
unique coprime pair `(p, q)` with `2 ≤ p < q` satisfying
`count(p, q) = 1`. The Pair Forcing theorem does *not* by itself
replace §5 or §6.5 (each argument uses distinct hypotheses);
rather, Cor 6.7.3 says that the three independent routes
converge on the same pair, which is then the unique option
common to all of them.

**Remark 6.7.4 (no-generalization).** The pair structure is rigid:
- Three or more atoms (`|A| ≥ 3`) yield *no* atomic `n`: Bézout
  shifts proliferate and always break uniqueness.
- Non-coprime atoms restrict `n` to multiples of `gcd`, losing the
  universal count theorem.
- Weakening the alive condition (non-odd multiplicities) contradicts
  the antisymmetric-multiplicity postulate (§6.6(c)).

Thus `(p, q, n) = (2, 3, 5)` is an **arithmetic fixed point** — the
axiom's only self-consistent numerical consequence.

---

## 7. Block structure and invariance

**Remark 7.0 (The partition comes from the firmware).** §1.3
already derived, from the axiom alone, the Level-2 closure
of the free-commutative-magma-without-fixed-points:

```
A-type: {a, b, a/b}        — 3 terms
B-type: {a/(a/b), b/(a/b)} — 2 terms
```

This (3, 2) partition is *not* an external choice — it is the
arithmetic of closure depths. The present section treats the
partition abstractly as `V := V_A ⊔ V_B` with `|V_A| = 3,
|V_B| = 2`, independent of the particular Raw terms realising
the parts. The alive postulate of §6.6(c) is not needed for the
partition itself; it is retained only for the arithmetic
atomicity theorem (Theorem 6.3), which gives an independent
confirmation that `n = 5` is the unique atomic vertex count.

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

*Proof.* (Lean: `E213.App.Simplex.block_constant_implies_aut_invariant`.)
For bijective partition-preserving `σ`, both `isA (σ i) = isA i` and
`σ i = σ j ↔ i = j` hold. Hence `classify (σ i) (σ j) = classify i j`.
Since `W = f ∘ classify`, the conclusion follows. ∎

**Theorem 7.6 (Invariance ⟹ Block-constancy).** Conversely, if `W`
is invariant under every partition-preserving bijection, then `W` is
block-constant.

*Proof (prose only; Lean formalization not provided).* We show
two pairs in the same block-pair class have equal `W`-values.
Given `σ ∈ S_3` on `V_A`, extend to a partition-
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

## 8. Aut-faithful Lens existence

We ask: when does the structure of §1–7 admit a Lens whose
automorphism behavior matches that of `Raw` itself? We do not
presuppose any specific target algebra; the conditions below are
imposed independently, and the existence and uniqueness of a
satisfying codomain are derived as a theorem. The identification of
this codomain with a familiar algebra is recorded only after the
derivation.

**Conditions on the codomain `K`.** We seek `K` carrying enough
structure to support the Lens framework with a meaningful
automorphism action. The minimal natural setting is an `ℝ`-algebra
satisfying:

- **(C1) Finite-dimensional over `ℝ`.** *Stipulation.* Lens values
  are determined inductively from `Fin 2` base data and a binary
  `combine`; an infinite-dimensional codomain would carry strictly
  more information (in the sense of `dim_ℝ K`) than the two base
  values and the binary operation provide. The axiom itself does
  not force this — infinite-dimensional ℝ-algebras with Aut_ℝ = ℤ/2
  could in principle arise; they are excluded here as extraneous to
  the two-generator / binary-operation scale of the axiom.
- **(C2) Commutative.** *Structural reflection of §1.1's "between".*
  The axiom names "two objects" symmetrically (the pair, not the
  ordered tuple); the Raw canonical form (§1.2) identifies
  `slash x y` with `slash y x`. Commutativity of `combine` at the
  Lens layer is the precise value-level translation. Dropping it
  admits `ℍ` (Cor 8.6), which the axiom's symmetric reading rejects
  via Aut mismatch; so (C2) is not only natural but enforced by
  Aut-faithfulness.
- **(C3) Unital.** *Stipulation.* A multiplicative identity is
  adopted to enable the field-classification step of Theorem 8.4.
  Non-unital ℝ-algebras (e.g. the augmentation ideal of a group
  algebra) could in principle satisfy the other conditions; they
  are excluded for classification-theoretic convenience, not by
  the axiom.
- **(C4) Division algebra.** *Structural reflection of
  non-degeneracy.* Every nonzero element invertible — a Lens value
  cannot vanish without the corresponding Raw term being
  absent. Without (C4), `ℝ ⊕ ℝ` (with coordinate-wise multiplication)
  satisfies the other conditions and has `|Aut_ℝ(ℝ ⊕ ℝ)| = 2` (the
  coordinate swap), which would falsely match Aut(Raw); (C4) excludes
  this false competitor.

Call this class `𝒞`.

**Status of (C1)–(C4).** Only (C2) is forced by Aut-faithfulness
(see Cor 8.6). Conditions (C1), (C3), (C4) are honest stipulations
chosen for the classification theorem to apply, not derivations
from the axiom alone. Relaxing any of (C1), (C3), (C4) would admit
additional codomains beyond ℂ — so the "uniqueness of ℂ" is
strictly *uniqueness within `𝒞`*, not *uniqueness among all
ℝ-algebras*.

*Reviewer honesty.* §8's theorem is: given the axiom + (C1)–(C4) +
Aut-faithfulness, the unique codomain is ℂ. It is not: the axiom
alone forces ℂ. The prose occasionally uses "forces" loosely;
this should be read inside the §8 hypothesis set.

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

**Theorem 8.4 (Existence and uniqueness in `𝒞`).** Within `𝒞`:

1. (Classification.) Up to `ℝ`-algebra isomorphism, `𝒞` contains
   exactly two elements: a one-dimensional one (call it `K_1`) and
   a two-dimensional one (call it `K_2`).
2. (Aut groups.) `|Aut_ℝ(K_1)| = 1` and `|Aut_ℝ(K_2)| = 2`.
3. (Faithful codomain.) Combined with `Aut(Raw) ≅ ℤ/2`
   (Theorem 3.5), exactly `K_2` admits an Aut-faithful Lens.

*Proof.*

(1) Every `K ∈ 𝒞` is a finite field extension of `ℝ`: (C2)+(C3)+(C4)
make `K` a field, and (C1) makes it algebraic over `ℝ`. Irreducible
polynomials over `ℝ` have degree `1` or `2` (fundamental theorem of
algebra applied to `ℝ[x]`), so `[K : ℝ] ∈ {1, 2}`. There is exactly
one isomorphism class at each dimension: dim `1` gives `ℝ` itself;
dim `2` gives the unique `ℝ`-algebra obtained by adjoining a root
of any monic irreducible quadratic (e.g. `x² + 1`).

(2) For `K_1` (dim `1`): any `ℝ`-algebra endomorphism is determined
by its value on `1`, which must be `1`. So `Aut_ℝ(K_1) = {id}`.
For `K_2` (dim `2`): write `K_2 = ℝ[α]` with `α² = -1`. Any
`σ ∈ Aut_ℝ(K_2)` is determined by `σ(α)`. From
`σ(α)² = σ(α²) = -1` we get `σ(α) = ±α`. So `|Aut_ℝ(K_2)| = 2`.

(3) Aut-faithfulness (Definition 8.3) requires
`|Aut(Raw)| = |Aut_ℝ(K)|`. By Theorem 3.5, `|Aut(Raw)| = 2`. From
(2), this matches only `K_2`; for `K_2` the unique nontrivial
group isomorphism `ρ : ℤ/2 → ℤ/2` lifts `swap` to the nontrivial
element of `Aut_ℝ(K_2)`. ∎

**Corollary 8.5 (Identification).** The two-dimensional `K_2 ∈ 𝒞`
of Theorem 8.4 is, by direct construction, the field of complex
numbers. Adjoining a root `α` of `x² + 1` to `ℝ` gives `ℝ[α]` with
`α² = -1`, which is the standard presentation of `ℂ` with `α = i`.
The nontrivial element of `Aut_ℝ(K_2)` is then complex conjugation
`i ↦ -i`. The unique Aut-faithful codomain in `𝒞` is therefore the
field `ℂ`, with `swap` lifted to conjugation.

**Corollary 8.6 (Non-commutative case excludes ℍ).** Dropping (C2)
from `𝒞` admits the quaternions `ℍ`, a finite-dim unital division
`ℝ`-algebra. However, `Aut_ℝ(ℍ) ≅ SO(3)` is a connected Lie group
of dimension `3`, and `|Aut(Raw)| = 2 ≠ |SO(3)|`. No group
isomorphism `Aut(Raw) ≅ Aut_ℝ(ℍ)` exists; hence `ℍ` admits no
Aut-faithful Lens. The commutativity condition (C2) is therefore
the decisive constraint separating the unique faithful codomain
`K_2` from `ℍ`.

**Remark 8.7 (On the remaining conditions in `𝒞`).** Corollary 8.6
has addressed (C2). The remaining conditions:
- *(C1) Finite-dim*: excludes infinite-dimensional `ℝ`-algebras
  (e.g., function algebras, formal power series). Needed to invoke
  the classification step (1) in Theorem 8.4.
- *(C3) Unital + (C4) Division*: exclude split algebras like
  `ℝ ⊕ ℝ` (which has zero divisors) and para-algebras without unit.

Each (C1)–(C4) is necessary for the existence-and-uniqueness
conclusion of Theorem 8.4.

**Remark 8.8 (Relation to Hurwitz–Frobenius).** The theorems of
Frobenius (finite-dim associative `ℝ`-division algebras are
`ℝ, ℂ, ℍ`) and Hurwitz (`ℝ`-composition algebras are
`ℝ, ℂ, ℍ, 𝕆`) play no external role here. Step (1) of the proof
uses only the commutative fragment of Frobenius (which reduces to
the elementary classification of finite `ℝ`-field extensions via
the fundamental theorem of algebra).

---

## Conclusion

The minimal system defined by the 3-clause axiom of §0 consists
of the following structure, presented here with precise
dependency tracking between claims. For each item we mark the
Lean formalisation status: **[✓]** fully proved; **[prose]**
informal proof only; **[partial]** some of the underlying
theorems proved, full statement informal.

**From the axiom (§1–3):**

1. **[✓]** A free commutative magma on two generators with no
   fixed points, emulated in Lean as the canonical-form subtype
   `Raw` of a free ordered magma (Definition 1.1). The two base
   tokens `a, b` plus the symmetric, anti-reflexive operator
   `slash` implement the three axiom clauses. No equality or
   apartness primitive is part of the axiom; the Lean encoding
   uses Lean's own propositional equality as external
   bookkeeping.

2. **[partial]** A single nontrivial Raw-automorphism (the swap
   involution): `Raw.swap` and its involution `Raw.swap_swap` are
   formalised (Lean: `E213.Firmware.Raw.swap_swap`). The statement
   `Aut(Raw) ≅ ℤ/2` of Theorem 3.5 itself is informal.

3. **[✓]** A Lens/catamorphism framework: every triple
   `(base_a, base_b, combine)` determines a unique
   `view : Raw → α` via `Raw.fold` (Theorem 4.5), with
   kernel-equivalence and refinement as natural operations.
   Equality on Raw becomes available as a Lens kernel; apartness
   is the negation of a Lens kernel and is thus Lens-dependent.

4. **[✓ subject to the §5 hypothesis]** The generalized
   signatures `RawNk` (Definition 5.1), **with a stipulated
   pairwise-distinctness constraint on relation arguments that
   the Raw axiom itself does not provide**, vacuously restrict to
   bases when `N < k` (Theorem 5.3) and to degenerate constants
   or chains when `k ∈ {0, 1}` (Corollary 5.4). Under the added
   constraint, `(N, k) = (2, 2)` is the minimal non-degenerate
   non-vacuous signature. The axiom does not force (2, 2) on its
   own; §5 imports the distinctness stipulation, and the word
   "forced" should be read inside §5's hypothesis, not outside.

**From the axiom together with §6–7 (with the antisymmetric-
multiplicity principle of §6.6(c) adjoined):**

5. **[✓]** The atom set `A = {2, 3}` is fixed by Proposition 6.5
   (non-decomposable integers `≥ 2`) combined with the structural
   choice `atoms ≥ 2` (§6.6(a)). The alive predicate is the
   antisymmetric-multiplicity principle (§6.6(c)) — *postulated*,
   not derived from the axiom. Together, `n = 5` is the unique
   atomic vertex count (Theorem 6.3), giving the canonical
   partition `V = V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2`.

5'. **[✓]** The arithmetic sharpening of §6.7 (Theorem 6.7.2,
   Pair Forcing): among all coprime pairs `(p, q)` with
   `2 ≤ p < q`, the unique pair satisfying `count(p, q) = 1` is
   `(p, q) = (2, 3)`. This does *not* by itself replace §5 or
   §6.5 — each argument uses distinct hypotheses; Cor 6.7.3
   merely says the three arguments converge on the same pair.

6. **[partial]** The `S_3 × S_2` action yields exactly six orbits
   on `V × V`, and invariance under this action is equivalent to
   block-constancy (Theorems 7.5–7.6). Lean formalizes the forward
   direction (7.5); the converse (7.6) is prose only.

**Within the class `𝒞` of codomains satisfying (C1)–(C4) of §8:**

7. **[prose]** There exists a unique element `K_2 ∈ 𝒞` (up to
   ℝ-algebra isomorphism) admitting an Aut-faithful Lens — one
   whose induced action matches `Aut(Raw) ≅ ℤ/2` exactly. By
   direct construction, this `K_2` is the field of complex
   numbers `ℂ` (Theorem 8.4 + Corollary 8.5). The non-commutative
   case (relaxing (C2)) admits `ℍ` but yields no Aut-faithful
   Lens (Corollary 8.6). §8 is entirely prose; no Lean
   formalization of Theorem 8.4 or its corollaries is provided.

---

**Honest summary.** The axiom forces: the free commutative magma
on 2 generators with no fixed points (§1); its catamorphism /
Lens framework (§4); and, as an arithmetic sharpening, the
unique coprime pair `(p, q) = (2, 3)` with `count(p, q) = 1`
(§6.7). The *choice* of (i) minimality among generalized
signatures (§5), (ii) the antisymmetric-multiplicity postulate
for the alive condition (§6.6(c)), and (iii) the class-`𝒞`
conditions (C1)–(C4) (§8) are each acknowledged as additional
structural stipulations, not derivations from the axiom alone.
`Aut(Raw) ≅ ℤ/2` and the ℂ-identification are proved at the
prose level; their Lean formalizations are partial and deferred.

This is the minimal system defined by "there is a relation."

End.
