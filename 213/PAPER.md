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

The derivation proceeds in six sections:

1. **Firmware (§1):** `Raw`, its three constructors, and its
   first closure levels. `Raw` is self-contained, carrying no
   equality or apartness primitive.
2. **Symmetry (§2):** swap automorphism, `Aut(Raw) ≅ ℤ/2`.
3. **Signature analysis (§3):** why `(2, 2)` is the minimal
   non-degenerate engine.
4. **Hypervisor (§4):** Lens framework; kernel-equivalence is
   the only notion of equality on `Raw`. The Lens must carry a
   codomain whose automorphism group receives `Aut(Raw) ≅ ℤ/2`
   faithfully — a constraint which motivates §6.
5. **Atomicity (§5):** arithmetic confirmation of `n = 5` and
   the `(3, 2)` partition already visible at Level 2 of §1.
6. **Algebraic projection (§6):** the unique codomain whose
   automorphism group matches `ℤ/2` is `ℂ`.

---

## 0. Notation and conventions

- `Fin n` denotes the standard `n`-element type `{0, …, n-1}`.
- `inductive T` denotes an initial algebra presentation: `T` is
  the smallest type closed under the listed constructors.
- All claims below are formally checked in Lean 4
  (`E213.*` modules, 0 `sorry`); we cite the Lean name where
  relevant, and mark "partial" or "prose only" when coverage is
  incomplete.
- The axiom does *not* supply an equality or inequality primitive
  on `Raw`. Lean's propositional equality is external bookkeeping;
  apartness is not part of `Raw`.

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

### 1.2 Lean encoding

Lean 4 core has no primitive quotient types on arbitrary relations,
and we import no set theory (no `Multiset`, no Mathlib). We encode
the target (Def 1.1) as a canonical-form subtype of a free ordered
magma. An auxiliary total order on trees picks a unique
representative per unordered pair; *the ordering is the encoding's
selection function, not a property of the axiom*.

This is the minimal Lean 4 native realisation of the intended
quotient — no external logical apparatus, no extra primitives.
Anti-reflexivity is realised by "strictly ordered children",
symmetry by "canonical form per unordered pair".

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
canonicalises child order; `Raw.slash_comm` certifies that both
input orderings collapse to the same Raw term — the axiom's
symmetric reading at the type level.

(Lean: `E213.Firmware.Raw.slash`, `E213.Firmware.Raw.slash_comm`.)

**Definition 1.2 (Depth).** `Raw.depth : Raw → ℕ` is `0` on base
tokens and `1 + max x.depth y.depth` on `slash x y`.

### 1.3 First three closure levels

Let the *level* of a Raw term be its depth. The closure by levels
is:

- **Level 0:** `{a, b}` — 2 terms.
- **Level 1:** add `a/b`, the unique unordered distinct pair from
  Level 0 — 3 terms total.
- **Level 2:** add `a/(a/b)` and `b/(a/b)`, the two new unordered
  distinct pairs involving a Level-1 term — 5 terms total.

The five Level-≤2 terms split as 3 + 2:

```
A-type (Levels 0+1): {a, b, a/b}        — 3 terms
B-type (Level 2):    {a/(a/b), b/(a/b)} — 2 terms
```

This `(3, 2)` split is a direct consequence of closure depth: it
requires no external postulate. §5 below is an arithmetic
confirmation of this count; the count itself is already settled
here.

(Lean: `E213.Firmware.Raw.level1_card`,
`E213.Firmware.Raw.level2_new_card`,
`E213.Firmware.Raw.level2_total_card` — the 5 terms are
formalised as an explicit list with `List.Nodup` verified by
`decide`.)

---

## 2. Symmetry of `Raw`

The axiom places `a, b` in a symmetric role: the choice of which
is "first" is not part of the axiomatic data. §2 makes this
precise as an endomorphism.

**Definition 2.1 (Swap).** The map `swap : Raw → Raw` exchanges
the two base tokens and extends through `slash` by structural
recursion:

```
  swap a           := b
  swap b           := a
  swap (slash x y) := slash (swap x) (swap y).
```

At the canonical-form level, swapping children may violate the
ordering invariant; Lean re-canonicalises after each swap. The
re-canonicalisation is an implementation detail of §1.2's
encoding with no semantic content.

(Lean: `E213.Firmware.Raw.swap`.)

**Theorem 2.2 (Involution).** `swap (swap x) = x` for all `x`.

*Proof.* Induction on `x`. Base: direct. Step: `swap (swap (x/y))
= swap (slash (swap x) (swap y)) = slash x y` by IH. ∎ (Lean:
`E213.Firmware.Raw.swap_swap`.)

**Corollary 2.3 (Bijectivity).** `swap` is a bijection of `Raw`.
(Lean: `E213.Firmware.Raw.swap_injective, swap_surjective,
swap_bijective`.)

**Definition 2.4 (Raw-automorphism).** A *Raw-automorphism* is a
bijection `φ : Raw → Raw` with `φ(slash x y h) = slash(φx)(φy)h'`
and `(φa, φb) ∈ {(a, b), (b, a)}`. Such `φ` is fixed by its
action on the base tokens.

**Theorem 2.5 (Automorphism group).** `Aut(Raw) ≅ ℤ/2`; its
nontrivial element is `swap`.

*Proof.* There are exactly two base permutations (identity and
swap); each extends uniquely to a Raw-endomorphism by Def 2.4.
Composition matches `S_2 ≅ ℤ/2`. ∎

**Lean coverage.** `Raw.swap_swap`, `Raw.swap_comp_swap`
(`swap ∘ swap = id`), and `Raw.swap_ne_id` (`swap ≠ id`)
formalise the ℤ/2 structure on `{id, swap}`. The full
classification "every Raw-automorphism is id or swap" is prose
only.

---

## 3. Signature analysis: why `(2, 2)`

Before building the Hypervisor, we ask whether the two-generator /
binary signature of `Raw` is itself constrained. If one imports a
pairwise-distinctness rule at the relation level (a rule the
axiom does not supply), the minimal non-degenerate signature is
`(N, k) = (2, 2)`. This confirms `(Fin 2, binary)` is the
smallest self-consistent engine; the axiom independently fixes
it from clauses (1)–(3).

**Definition 3.1 (Generalised Raw).** For `N, k : ℕ`:

```
inductive RawNk (N k : Nat)
  | object : Fin N → RawNk
  | rel    : (Fin k → RawNk) → RawNk,
```

with reachability:

```
  base : Reachable (object i)
  step : (∀ i, Reachable (f i)) →
         (∀ i j, i ≠ j → f i ≠ f j) →
         Reachable (rel f).
```

**Lemma 3.2 (Pigeonhole).** For `N < k`, no injection
`Fin k → Fin N` exists.

(Lean: `E213.OS.Pigeonhole.no_inj_lt`.)

**Theorem 3.3 (Vacuousness for `N < k`).** Every Reachable term
of `RawNk N k` with `N < k` is a base object.

*Proof.* Induction on the Reachable derivation; the step case
lifts to a `Fin k → Fin N` injection, contradicting Lemma 3.2.
(Lean: `E213.OS.ArityForcingGeneral.reachable_base_only`.) ∎

**Corollary 3.4 (Minimal engine).** Non-vacuity requires `N ≥ k`;
arities `k = 0, 1` are degenerate (constants / linear chains).
The minimal non-degenerate, non-vacuous signature is therefore
`(N, k) = (2, 2)`, agreeing with §1.1.

**Scope.** §3's "forced" reads inside the imported distinctness
hypothesis. The axiom of §1 independently fixes `(Fin 2, binary)`;
§3 is a sanity-check convergence.

---

## 4. Hypervisor: the Lens framework

`Raw` by itself carries no notion of equality — anti-reflexivity
and symmetry live inside the type, but "same value" between
distinct Raw terms is undefined. §4 introduces **Lenses**, which
supply codomains together with a binary operation and provide the
*only* route by which equality on `Raw` becomes meaningful.

**Definition 4.1 (Lens).** A `Lens` with codomain `α` is a triple

```
  Lens α = (base_a : α, base_b : α, combine : α → α → α).
```

**Definition 4.2 (View / catamorphism).** For `L : Lens α`,

```
  L.view a               := L.base_a
  L.view b               := L.base_b
  L.view (slash x y h)   := L.combine (L.view x) (L.view y).
```

`L.view` is implemented in Lean as a wrapper over `Raw.fold`; the
Hypervisor layer does not reference `Tree`.

**Definition 4.3 (Kernel equivalence).** `L.equiv x y :=
L.view x = L.view y`. This is the kernel equivalence of `L.view`
— an equivalence relation on `Raw`. **The axiom's absent
equality primitive is supplied here, Lens by Lens.**

**Definition 4.4 (Refinement).** `L` *refines* `M` iff
`∀ x y, L.equiv x y → M.equiv x y`; equivalently, `M.view`
factors through `L.view`.

**Theorem 4.5 (Catamorphism compatibility, symmetric case).** For
`α`, base values `aα, bα`, and **symmetric** `c : α → α → α`, the
view of `⟨aα, bα, c⟩` satisfies

```
  view a = aα,
  view b = bα,
  view (slash x y h) = c (view x) (view y).
```

Non-symmetric `c` admits no such view, because
`slash x y h = slash y x h'` would force
`c u v = c v u` on the image. (Lean: `E213.Firmware.Raw.fold_a,
fold_b, fold_slash`.)

### 4.6 Foreshadowing the codomain

The Lens framework has a structural consequence we will not fully
cash out until §6. The symmetry `Aut(Raw) ≅ ℤ/2` of §2 means
every Raw carries an order-2 symmetry natively. A Lens whose
codomain faithfully reflects this symmetry must itself have a
two-element automorphism group acting consistently with `swap`.

That is, §4's Lens framework does not merely provide equality —
it poses a constraint on candidate codomains: *the codomain must
receive `ℤ/2` faithfully*. Among ℝ-algebras, only one does. §6
spells this out.

---

## 5. Atomicity and the `(3, 2)` partition

§1.3 already derived the `(3, 2)` split of Level-≤2 Raw terms
directly from the axiom's closure. §5 confirms this by an
independent arithmetic argument: among integers `n`, there is a
unique `n` admitting a canonical decomposition into 2-blocks and
3-blocks of maximal symmetry, and that `n` is `5`. The arithmetic
agrees with the closure count — no external postulate enters the
value `5`.

### 5.1 From genealogy to arithmetic

The Level-2 closure has exactly five terms split `3 + 2`. Reading
the split as "one 3-atom and one 2-atom", we ask: for which `n`
does `n = 2a + 3b` admit a canonical decomposition?

**Definition 5.1 (Alive, genealogical reading).** A decomposition
`(a, b) ∈ ℕ²` of `n = 2a + 3b` is *alive* iff both `a` and `b`
are odd. **Observation.** At the Level-2 closure `(a, b) = (1, 1)`,
the decomposition is alive by definition (both coefficients equal
to 1). The "alive" predicate thus formalises the minimal
genealogical reading: *each atom type appears in the Level-2
closure with odd multiplicity*, and paired copies of a structurally
identical atom collapse under canonical form (§1.2). No external
axiom is introduced; the predicate names the Level-2 pattern.

**Definition 5.2 (Atomic).** `n` is *atomic* iff `n = 2a + 3b`
has a unique pair `(a, b) ∈ ℕ²` and that pair is alive.

**Theorem 5.3 (Atomicity).** `n ∈ ℕ` is atomic iff `n = 5`.

*Proof.* (Lean: `E213.OS.Atomicity.atomic_iff_five`.)

*Existence at `n = 5`.* `3b ≤ 5` gives `b ∈ {0, 1}`; `b = 0` is
impossible; `b = 1` gives `a = 1`. Unique decomposition `(1, 1)`,
alive.

*Only `n = 5`.* Let `(a, b)` be the unique alive decomposition.
The Bézout shift `(a, b) ↦ (a ± 3, b ∓ 2)` preserves `2a + 3b`.
If `a ≥ 3`, `(a - 3, b + 2) ∈ ℕ²` is a second decomposition,
contradicting uniqueness; hence `a < 3`. If `b ≥ 2`,
`(a + 3, b - 2) ∈ ℕ²` is a second decomposition; hence `b < 2`.
With `a, b` odd nonnegative, `a = b = 1`, giving `n = 5`. ∎

**Corollary 5.4 (Canonical partition).** The unique atomic `n`
admits `(1, 1)`: one 2-block, one 3-block, total 5 vertices
split as `V = V_A ⊔ V_B` with `|V_A| = 3, |V_B| = 2`. This
matches §1.3 exactly.

### 5.2 The atom set `{2, 3}`

**Proposition 5.5 (Non-decomposability).** An integer `n ≥ 2`
cannot be written `n = n_1 + ⋯ + n_k` with `k ≥ 2` and each
`n_i ≥ 2` iff `n ∈ {2, 3}`.

*Proof.* (Lean: `E213.OS.NonDecomposable.non_decomposable_iff`.)
A multi-part decomposition collapses to 2 parts. Direct case
analysis: `n ∈ {2, 3}` gives `a + b ≥ 4 > n`, impossible; `n = 4`
is `2 + 2`; `n ≥ 5` is `2 + (n - 2)`. ∎

The atom values `{2, 3}` are thus fixed by pure arithmetic: the
two integers with no non-trivial self-composition above the
lower bound `≥ 2`. The lower bound itself is a genealogical
choice: atoms are Raw-subtrees that *use* the `slash` constructor
at least once, so leaves count `≥ 2`.

*Primitive-data echo.* The same two sizes occur as the base pair
`|{a, b}| = 2` and the Level-1 closure `|{a, b, a/b}| = 3`. (Lean:
`E213.OS.PrimitiveSizes.primitive_sizes_eq_nondecomposable`.) The
arithmetic of Proposition 5.5 is what fixes `A`; the echo is for
intuition.

### 5.3 Pair Forcing

§5.1–5.2 fix `(A, n) = ({2, 3}, 5)` given that atoms form a coprime
pair. A sharper question: among *all* coprime pairs `(p, q)` with
`2 ≤ p < q`, which pair has a unique "atomic" vertex count in the
sense of Definition 5.2?

**Definition 5.6 (Count).** For `p, q ≥ 2`,
```
  count(p, q) := ⌊p/2⌋ · ⌊q/2⌋.
```

*Combinatorial interpretation.* `⌊q/2⌋` counts odd positive
integers less than `q`; `⌊p/2⌋` those less than `p`. Under the
Bézout uniqueness bound `a < q ∧ b < p`, the count of odd-positive
solution pairs is `⌊p/2⌋ · ⌊q/2⌋`. We do not formalise the
"count = #atomic" bijection for general `(p, q)` in Lean; Theorem
5.7 is stated as a pure arithmetic identity.

**Theorem 5.7 (Pair Forcing).** For coprime `p, q` with
`2 ≤ p < q`,

```
  count(p, q) = 1  ⟺  (p, q) = (2, 3).
```

*Proof.* `⌊p/2⌋ ≥ 1` and `⌊q/2⌋ ≥ 1` from `p, q ≥ 2`; their
product equals 1 iff both equal 1. `⌊k/2⌋ = 1 ⟺ k ∈ {2, 3}`. With
`p < q` coprime, the unique solution is `(2, 3)`. ∎ (Lean:
`E213.OS.PairForcing.count_eq_one_iff`.)

**Corollary 5.8.** The arithmetic atom-pair `(2, 3)` — fixed
independently by §3 (arity 2, minimality under distinctness),
§5.2 (atom values, non-decomposability), and §5.3 (count = 1,
coprime) — is the unique option common to all three independent
routes.

**Remark 5.9 (Rigidity).** The structure is narrow:

- Three or more atoms (`|A| ≥ 3`) yield *no* atomic `n`: Bézout
  shifts proliferate and always break uniqueness
  (`foundations/experiments/FND_042`).
- Non-coprime atoms restrict `n` to multiples of `gcd`, losing
  the universal count theorem.

Thus `(p, q, n) = (2, 3, 5)` is an arithmetic fixed point:
altering any of arity, atom values, or the genealogical Level-2
reading destroys the uniqueness.

---

### 5.4 Block structure and invariance

*(This subsection was §7 in the previous draft; it sits naturally
as the continuation of §5 because it formalises the action of
`S_3 × S_2` on the `(3, 2)` partition already established above.
We retain a separate heading for navigability.)*

Take `V := Fin 5`, `V_A := {0, 1, 2}`, `V_B := {3, 4}`.

**Definition 5.4.1.** `isA : Fin 5 → Bool`, `isA i := (i.val < 3)`.

**Definition 5.4.2 (Block-pair classifier).**
`classify : Fin 5 × Fin 5 → BlockPair`, with six cases:

```
AAdiag    3 pairs   AAoff   6 pairs    AB    6 pairs
BA        6 pairs   BBdiag  2 pairs    BBoff 2 pairs
                                      — total 25 = |V|²
```

**Definition 5.4.3 (Partition-preserving permutation).** Bijection
`σ : Fin 5 → Fin 5` with `isA (σ i) = isA i` for all `i`. The
group of such bijections is `S_{V_A} × S_{V_B} ≅ S_3 × S_2`, of
order 12.

**Definition 5.4.4 (Block-constant weight).**
`W : Fin 5 × Fin 5 → α` is *block-constant* iff it factors through
`classify`.

**Theorem 5.4.5 (Block-constancy ⟹ invariance).** Block-constant
`W` is invariant under every partition-preserving bijection.

*Proof.* A partition-preserving bijection preserves `classify`;
`W = f ∘ classify` then gives the claim. ∎ (Lean:
`E213.App.Simplex.block_constant_implies_aut_invariant`.)

**Theorem 5.4.6 (Invariance ⟹ block-constancy).** Conversely, if
`W` is invariant under every partition-preserving bijection, then
`W` is block-constant.

*Proof (prose only; not formalised in Lean).* Use transitivity of
`S_3` on the 6 ordered distinct pairs of `V_A` (free action,
`|S_3| = 6`), of `S_2` on the 2 ordered distinct pairs of `V_B`
(free action, `|S_2| = 2`), and of each factor on its own
diagonal. Invariance under these actions collapses each class to
a single value. ∎

---

## 6. Algebraic projection: the unique codomain is `ℂ`

§2 established `Aut(Raw) ≅ ℤ/2`. §4 posed the Hypervisor
constraint: a Lens whose codomain receives this symmetry
faithfully gives `Raw` its "full expressive reach". §6 now
identifies the codomain.

### 6.1 The class 𝒞

We seek an ℝ-algebra `K` satisfying:

- **(C1) Finite-dimensional over ℝ.** *Stipulation.* The Lens
  is parameterised by two base values and one binary operation;
  infinite-dimensional codomains carry more information than the
  axiom's two-generator / binary-operation scale provides.
  Infinite-dim ℝ-algebras with `Aut_ℝ = ℤ/2` could in principle
  exist; we exclude them as extraneous.
- **(C2) Commutative.** *Structural reflection.* §1's canonical
  form identifies `slash x y = slash y x`; commutativity of
  `combine` at the Lens layer is the value-level translation.
  Dropping (C2) admits `ℍ` (Cor 6.6), whose
  `Aut_ℝ(ℍ) ≅ SO(3)` does not match `ℤ/2`; so (C2) is *enforced
  by Aut-faithfulness*, not merely stipulated.
- **(C3) Unital.** *Stipulation.* A multiplicative identity is
  adopted to reach the field-classification step of Thm 6.4.
  Non-unital ℝ-algebras could satisfy the remaining conditions;
  they are excluded for classification-theoretic convenience.
- **(C4) Division algebra.** *Non-degeneracy.* Every nonzero
  element is invertible — a Lens value cannot vanish without the
  corresponding Raw term being absent. Without (C4),
  `ℝ ⊕ ℝ` (with `|Aut_ℝ| = 2`) would falsely match; (C4) excludes
  this competitor.

Call this class `𝒞`.

**Status.** Only (C2) is forced by Aut-faithfulness (Cor 6.6);
(C1), (C3), (C4) are stipulations chosen for the classification
theorem to apply. "Uniqueness of `ℂ`" is uniqueness *within* `𝒞`,
not uniqueness among all ℝ-algebras.

### 6.2 Existence and uniqueness

**Definition 6.1.** `Aut_ℝ(K)` is the group of ℝ-algebra
automorphisms of `K`.

**Definition 6.2 (Aut-equivariance).** A Lens `L` with codomain
`K ∈ 𝒞` is *Aut-equivariant* iff there is a group homomorphism
`ρ : Aut(Raw) → Aut_ℝ(K)` with
`L.view (τ x) = ρ(τ) (L.view x)`.

**Definition 6.3 (Aut-faithfulness).** `L` is *Aut-faithful* iff
`ρ` is a group *isomorphism* `Aut(Raw) ≅ Aut_ℝ(K)`.

**Theorem 6.4 (Existence and uniqueness in `𝒞`).** Within `𝒞`:

1. *(Classification.)* Up to ℝ-algebra isomorphism, `𝒞` has
   exactly two elements: one-dimensional `K_1` and
   two-dimensional `K_2`.
2. *(Aut groups.)* `|Aut_ℝ(K_1)| = 1`, `|Aut_ℝ(K_2)| = 2`.
3. *(Faithful codomain.)* Combined with `Aut(Raw) ≅ ℤ/2`
   (Thm 2.5), exactly `K_2` admits an Aut-faithful Lens.

*Proof (prose; not formalised in Lean).*

(1) Every `K ∈ 𝒞` is a finite field extension of ℝ
((C2)+(C3)+(C4)+(C1)). Irreducible polynomials over ℝ have
degree 1 or 2; so `[K : ℝ] ∈ {1, 2}`, with one isomorphism class
per dimension.

(2) For `K_1`, any ℝ-algebra endomorphism fixes 1, hence `K_1`.
For `K_2 = ℝ[α]` with `α² = -1`, `σ(α)² = -1` gives `σ(α) = ±α`;
`|Aut_ℝ(K_2)| = 2`.

(3) Aut-faithfulness requires `|Aut_ℝ(K)| = 2`; only `K_2` fits.
∎

**Corollary 6.5 (Identification with `ℂ`).** `K_2` is, by
construction, the complex numbers. Adjoining a root of `x² + 1`
to ℝ gives `ℝ[i]` with `i² = -1`, the standard presentation of
`ℂ`. The nontrivial element of `Aut_ℝ(K_2)` is complex
conjugation `i ↦ -i`. The unique Aut-faithful codomain in `𝒞` is
`ℂ`, with `swap` lifted to conjugation.

**Corollary 6.6 (`ℍ` excluded).** Dropping (C2) admits `ℍ`
(finite-dim unital division ℝ-algebra). `Aut_ℝ(ℍ) ≅ SO(3)` is a
Lie group of dim 3; `|Aut_ℝ(ℍ)| ≠ 2`. No Aut-faithful Lens over
`ℍ` exists. (C2) is therefore the decisive constraint separating
`K_2` from `ℍ`.

**Remark 6.7 (Relation to Hurwitz–Frobenius).** Frobenius's
theorem plays no external role; step (1) of Thm 6.4 uses only
the commutative fragment, which reduces to FTA + finite
ℝ-field-extension classification.

---

## Conclusion

The minimal system defined by the 3-clause axiom consists of the
following, with Lean status tags **[✓]** fully formalised,
**[partial]** some underlying theorems formalised, or
**[prose]** informal only.

**From the axiom (§1):**

1. **[✓]** `Raw`, the free commutative magma on two generators
   with no fixed points (Def 1.1). Lean 4 core realisation as a
   canonical-form subtype of a free ordered magma; no equality
   or apartness primitive imported.

2. **[✓]** The `(3, 2)` partition is visible directly in the
   closure: 5 Raw terms at Level ≤ 2 split 3 + 2 (§1.3).

**From the axiom + symmetry (§2):**

3. **[partial]** A single nontrivial Raw-automorphism, the swap
   involution, realising `Aut(Raw) ≅ ℤ/2`. Formalised:
   `Raw.swap`, `Raw.swap_swap`, `Raw.swap_comp_swap`,
   `Raw.swap_ne_id` — the ℤ/2 structure on `{id, swap}`. The
   full classification (Thm 2.5) is prose only.

**Meta-analysis (§3):**

4. **[✓ under imported distinctness]** `(N, k) = (2, 2)` is the
   minimal non-degenerate non-vacuous signature (Thm 3.3,
   Cor 3.4). The axiom independently fixes this from §1; §3 is
   a convergence sanity-check.

**Hypervisor (§4):**

5. **[✓]** Lens framework with catamorphism `Raw.fold`, kernel
   equivalence as the only notion of equality on Raw.
   Symmetric-`combine` catamorphism universal property
   (Thm 4.5).

**Arithmetic confirmation (§5):**

6. **[✓]** `n = 5` is the unique atomic vertex count (Thm 5.3)
   — independent arithmetic matching the Level-2 closure count
   of §1.3.

6'. **[✓]** Atom values `{2, 3}` are the non-decomposable
   integers ≥ 2 (Prop 5.5).

6''. **[✓]** Pair Forcing (Thm 5.7): among all coprime pairs
   with `2 ≤ p < q`, `count(p, q) = 1 ⟺ (p, q) = (2, 3)`. The
   three routes (§3, §5.2, §5.3) converge on the same pair.

6'''. **[partial]** `S_3 × S_2`-invariance on `V × V` equivalent
   to block-constancy (Thms 5.4.5–5.4.6). Lean formalises the
   forward direction; the converse is prose only.

**Algebraic projection (§6):**

7. **[prose]** Within `𝒞` (the class of ℝ-algebras satisfying
   (C1)–(C4)), the unique codomain admitting an Aut-faithful
   Lens is `ℂ` (Thm 6.4, Cor 6.5). No Lean formalisation; proof
   relies on finite-dimensional ℝ-field-extension theory.

---

### Honest summary

The axiom **forces**:

- `Raw` as the free commutative magma on 2 generators, no fixed
  points (§1);
- `Aut(Raw) ≅ ℤ/2` on the algebraic level (§2);
- `(3, 2)` partition at Level 2 of the closure (§1.3);
- the Lens framework as the only native route to equality on
  `Raw` (§4);
- `n = 5` as the unique atomic decomposition value (§5).

The axiom **does not force** (acknowledged stipulations):

- atom lower bound `≥ 2` in §5.2 (structural choice);
- class-`𝒞` conditions (C1), (C3), (C4) in §6 — only (C2) is
  Aut-enforced;
- finite classification machinery used in the prose proofs of
  Thm 2.5, Thm 6.4.

`Aut(Raw) ≅ ℤ/2` and the `ℂ`-identification are proved at the
prose level; their full Lean formalisations are partial or
absent. The "alive" predicate of §5.1 is *not* an external
postulate but an observation about the Level-2 closure, encoded
as odd-multiplicity — the Lean file retains the older name
`AliveFromDistinctness` for historical continuity but the status
is that of a structural observation, not an axiom.

This is the minimal system defined by the 3-clause axiom.

End.
