# Graded Residue Arithmetic — Book

**A Textbook Treatment of the Universal Meta-Structure of 213**

Status: CLOSED (Marathon 16 — GRA Universality, all 6 phases)
Lean source: `lean/E213/Lib/Math/GRA/` (8 files, ~1400 lines, 0 sorry)
Prerequisites: Basic familiarity with 213's P = [[2,1],[1,1]], K_{3,2}, and resolution lattice.

> **Closure note.** The marathon establishes a Lean-verified
> typeclass `GRAModel` with five instances (NumberTheory, Graph,
> Analysis, Cohomology, HoTT, HigherAlgebra), pairwise isos via the
> NT hub, and a translation programme including the universal
> depth-comparison theorem `⌈n/3⌉ ≤ (n+1)/2` valid in all five
> Readings simultaneously.  Purity: 0 `sorry`, 0 `Classical`, 0
> Mathlib; `propext`/`Quot.sound` are present (Tier 5.1
> propext-unsealing backlog).  Carriers are currently simplified
> (Nat = grade directly); enrichment to actual Walk / Cochain /
> operad objects is the optional Phase 7.

---

## Chapter 0 — Motivation: What Is This Book About?

### 0.1 The One Question

213 asks a single question:

> **When you make a distinction, what structure does the residue have?**

The answer turns out to be a 2×2 matrix P = [[2,1],[1,1]] with det=1,
whose action generates a graded arithmetic on the natural numbers.
This book develops that arithmetic — **Graded Residue Arithmetic (GRA)** —
from first principles, proves its core theorems, and shows how it
manifests across five independent mathematical domains.

### 0.2 Why "Graded Residue"?

- **Residue**: what remains after a distinction act. Not the thing distinguished,
  but the *trace* of the act itself.
- **Graded**: these residues carry a natural number label (grade) measuring
  "how many elementary distinctions were composed to produce it."
- **Arithmetic**: the grades form a semiring under two operations (⊕ = independent
  juxtaposition, ⊗ = interactive composition).

### 0.3 How to Read This Book

- **Chapter 1**: Raw structure — P, its generators, the grade function.
- **Chapter 2**: Core theorems — universal reachability, greedy optimality, depth.
- **Chapter 3**: The five Readings — how GRA appears in five mathematical fields.
- **Chapter 4**: Structural invariants — det=1, gcd=1, Frobenius=1.
- **Chapter 5**: GRA Tower and CD Tower duality.
- **Chapter 6**: Number system unification.
- **Chapter 7**: Formalizability assessment — what can be Lean-proved today.
- **Chapter 8**: Open frontiers.

Definitions are numbered. Theorems have proof sketches (full proofs
are in Lean files where available). Lean file references are given
in brackets: `[ResolutionShift.lean]`.

---

## Chapter 1 — The Raw Structure

### Definition 1.1 (The P-matrix)

```
P = [[2, 1],    ∈ SL(2, ℤ)
     [1, 1]]

det(P) = 2·1 − 1·1 = 1
trace(P) = 3
eigenvalues: φ² = (3+√5)/2, 1/φ² = (3−√5)/2
```

P is the **unique** 2×2 matrix over ℕ with:
- All entries positive
- det = 1
- Minimal trace (trace = 3 is the minimum for SL(2,ℤ) with all-positive entries)
- Row 1 = (NT, 1) where NT = 2 (temporal generator count)
- Row 2 = (1, 1) (Fibonacci shift structure)

### Definition 1.2 (Generators)

From P's first row and column structure:

- **NT = 2**: the "temporal" or "edge" generator
- **NS = 3**: the "spatial" or "face" generator (= trace(P))
- **d = NT + NS = 5**: the "total dimension" (= number of vertices in K_{3,2})

These satisfy: **gcd(NT, NS) = gcd(2, 3) = 1**.

### Definition 1.3 (P-Generation Set — PGen)

```
PGen = {n ∈ ℕ : ∃ a,b ≥ 0, n = 2a + 3b}
     = {0, 2, 3, 4, 5, 6, 7, 8, ...}
     = ℕ \ {1}     (for n ≥ 2, all are reachable)
```

[Lean: `Mobius213/Px/` — `pgen_iff`]

### Definition 1.4 (Grade / Depth)

For n ∈ PGen (n ≥ 2):

```
minDepth(n) = min { a + b : 2a + 3b = n, a,b ≥ 0 }
```

**Proposition 1.5** (Depth formula): `minDepth(n) = ⌈n/3⌉`

*Proof sketch*: Write n = 3q + r with r ∈ {0, 1, 2}.
- r = 0: use (a,b) = (0, q), depth = q = ⌈n/3⌉.
- r = 1: use (a,b) = (2, q−1) since 4 + 3(q−1) = 3q+1 = n, depth = q+1 = ⌈n/3⌉.
- r = 2: use (a,b) = (1, q) since 2 + 3q = 3q+2 = n, depth = q+1 = ⌈n/3⌉.

In all cases minDepth(n) = ⌈n/3⌉. Optimality follows from Theorem 2.2. □

### Definition 1.6 (Hom-set)

For m, n ∈ ℕ≥1:

```
Hom_GRA(m, n) = { (a, b) ∈ ℕ×ℕ : 2a + 3b = n − m }   if n > m
Hom_GRA(n, n) = { id }
Hom_GRA(m, n) = ∅                                       if m > n
```

**Proposition 1.7**: |Hom_GRA(m, n)| = ⌊(n−m)/6⌋ + δ  where δ ∈ {0, 1}
depending on residue class of (n−m) mod 6.

*Proof*: The number of solutions to 2a + 3b = k in non-negative integers
is ⌊k/6⌋ + 1 if k ≡ 0,2,3,4,5 (mod 6), and ⌊k/6⌋ if k ≡ 1 (mod 6).
For k ≥ 2: always at least one solution. For k = 1: no solution (the "gap"). □

---

## Chapter 2 — Core Theorems

### Theorem 2.1 (Universal Reachability)

> For all n ≥ 2: n ∈ PGen. Equivalently, Hom_GRA(0, n) ≠ ∅ for n ≥ 2.

*Proof*: gcd(2,3) = 1 and Chicken McNugget theorem give Frobenius(2,3) = 1.
So the only unreachable positive integer is 1. □

[Lean: `pgen_complete` in Mobius213/Px/]

### Theorem 2.2 (Greedy Optimality)

> For all n ≥ 2: the greedy algorithm (maximize b, i.e., use as many 3s as
> possible) achieves minDepth(n).

*Proof*: Let (a*, b*) achieve minDepth. Suppose a* ≥ 3. Then replace
(a*, b*) with (a*−3, b*+2): same n, but depth decreases by 1. Contradiction.
So a* ∈ {0, 1, 2}, which is exactly what greedy produces. □

[Lean: formalizable, not yet a standalone file]

### Theorem 2.3 (Composition Additivity — Gap 1 Resolution)

> If f has grade E₁ and g has grade E₂ (as resolution shifts),
> then g ∘ f has grade E₁ + E₂. (EQUALITY, not inequality.)

*Proof*: Direct from `IsResolutionShift_compose` — if f shifts resolution
by E₁ and g by E₂, their composition shifts by E₁ + E₂ pointwise. □

[Lean: `IsResolutionShift_compose` in Analysis/ResolutionShift.lean]

### Theorem 2.4 (Multiplicative Sub-additivity — Gap 1 Resolution)

> In a graded ring, grade(a · b) ≤ grade(a) + grade(b). (INEQUALITY.)

*Proof*: Multiplication can produce cancellation. Example: in a polynomial ring,
deg(x² · x³) = 5 = deg(x²) + deg(x³) (equality holds). But
deg((x+1)(x−1)) = deg(x²−1) = 2 < deg(x+1) + deg(x−1) = 1+1 = 2.
Actually equality holds here too. The inequality is strict only when
**leading terms cancel** — which is impossible for monomials but possible
for general elements.

**Resolution of Gap 1**: The distinction is:
- **⊕ (= independent composition, no interaction)**: Always equality.
  Because independent systems cannot interfere. Formalized as
  `IsResolutionShift_compose`: sequential application without cancellation.
- **⊗ (= interactive product, possible cancellation)**: At most equality.
  Because interaction can produce "destructive interference."
  Formalized as `grade_mul` in GradedRing213.

**Structural principle**: ⊕ is *free* (no relations between summands);
⊗ is *non-free* (relations/cancellations possible). This is why ⊕ gives
equality and ⊗ gives inequality. □

### Theorem 2.5 (One-Way Arrow / Irreversibility)

> `cutDouble` (= resolution coarsening) cannot carry a ℕ-grade.

*Proof*: If cutDouble had grade g ∈ ℕ, then cutDouble ∘ cutHalf would have
grade g + 1 ≥ 1. But cutDouble ∘ cutHalf = id (on appropriate domain),
which has grade 0. Contradiction since g + 1 ≠ 0. □

[Lean: `cutDouble_no_grade` in Analysis/ResolutionShift.lean]

**Interpretation**: Grade can only accumulate (increase). This is the
algebraic shadow of:
- Entropy increase (physics)
- Resolution refinement only (analysis)
- PGen only generates positives (arithmetic)

### Theorem 2.6 (Grade Uniqueness)

> If f has grade E₁ and grade E₂ (both as resolution shifts), then E₁ = E₂.

*Proof*: If f shifts resolution by E₁ and also by E₂, then for any
input (M, E): output has resolution E + E₁ = E + E₂, so E₁ = E₂. □

[Lean: `IsResolutionShift_grade_unique` in Analysis/ResolutionShift.lean]

---

## Chapter 3 — The Five Readings

### 3.0 What "Reading" Means (Gap 2 Resolution)

**Definition 3.0.1 (GRA Model)**

A **(2,3)-GRA model** is a quintuple (S, grade, ⊕, ⊗, depth) where:
- S is a set (the "graded objects")
- grade : S → ℕ
- ⊕ : S × S → S satisfies grade(a ⊕ b) = grade(a) + grade(b)
- ⊗ : S × S → S satisfies grade(a ⊗ b) ≤ grade(a) + grade(b)
- depth : S → ℕ satisfies depth(a) = minDepth(grade(a))
- The grade image contains {2, 3} (generators exist)
- The grade image = ℕ≥2 ∪ {0} (universal reachability)

**Definition 3.0.2 (GRA Model Morphism)**

A morphism between (2,3)-GRA models (S₁, ...) → (S₂, ...) is a function
f : S₁ → S₂ that preserves grade, commutes with ⊕ and ⊗, and preserves depth.

**Definition 3.0.3 (Reading)**

A "Reading" of GRA is a specific (2,3)-GRA model drawn from a mathematical
domain. The claim "R_i ≅ R_j" means there exists an invertible GRA model
morphism between them.

**Important clarification**: The Readings are NOT isomorphic as mathematical
structures in their native categories (cohomology rings ≇ Banach spaces).
They are isomorphic **only at the GRA-grade level** — i.e., the grade/depth/
operation structure is the same, even though the underlying objects are different.

This is analogous to: ℤ and 2ℤ are isomorphic as groups, but live in
different "universes" (one is a ring, the other is an ideal). The isomorphism
is at the group level only.

### 3.1 Reading₁ — Cohomology

| GRA element | Cohomological meaning |
|---|---|
| Grade n | Cochain degree n: element of Cⁿ |
| 2 (NT) | Edge coboundary δ⁰: C⁰ → C¹ shifts grade by 1; two applications = grade 2 |
| 3 (NS) | Face dimension: the 3 simple 4-cycle faces in K_{3,2}^{(c=2)} |
| ⊕ | Cup-grade sum: α ∈ Cᵏ, β ∈ Cˡ → α ⌣ β ∈ Cᵏ⁺ˡ |
| ⊗ | Cup product itself (non-linear: can kill classes) |
| Depth | Cup-length: minimum number of cup-factors to reach degree n |

**GRA model verification**:
- grade(α ⌣ β) = grade(α) + grade(β) ✓ (cup product is bigraded)
- depth = cup-length = ⌈n/3⌉ for K_{3,2} cohomology ✓
- Generators: δ gives grade-2 steps, face inclusion gives grade-3 steps ✓

[Lean evidence: `Cohomology/Cup/`, `Cohomology/Bipartite/`]

### 3.2 Reading₄ — Graph Theory

| GRA element | Graph-theoretic meaning |
|---|---|
| Grade n | Walk of length n in K_{3,2}^{(c=2)} |
| 2 (NT) | T-vertex count (= one side of bipartition) |
| 3 (NS) | S-vertex count (= other side), eigenvalue 0 multiplicity |
| ⊕ | Path concatenation: walk(a) · walk(b) = walk(a+b) |
| ⊗ | Graph tensor product (Kronecker product of adjacencies) |
| Depth | Shortest walk between vertices, ≈ distance |

**GRA model verification**:
- grade(concat(w₁, w₂)) = len(w₁) + len(w₂) ✓
- Generators: 2-step = T-to-T walk, 3-step = S-to-S-to-S walk ✓
- Universal reachability: any vertex reachable in ≤ n steps for n ≥ 2 ✓

### 3.3 Reading₅ — Analysis / Continuum

| GRA element | Analytic meaning |
|---|---|
| Grade E | Resolution exponent: precision level 2⁻ᴱ |
| 2 (NT) | Dyadic base: cutHalf = grade-1 generator |
| 3 (NS) | First non-trivial polynomial degree: x³ has depth 3n |
| ⊕ | Modulus composition: E₁ + E₂ resolution shift |
| ⊗ | Polynomial depth multiplication |
| Depth | linearityModulus: smoothness measure |

**GRA model verification**:
- `IsResolutionShift_compose`: grade(g∘f) = grade(g) + grade(f) ✓
- cutHalf = grade 1, cutHalf^n = grade n ✓
- Universal: all positive exponents reachable ✓

[Lean: `Analysis/ResolutionShift.lean`, `Topology/ModulusStructure.lean`]

### 3.4 Reading₂ — Higher Algebra (Operads)

| GRA element | Operadic meaning |
|---|---|
| Grade n | E_n-operad level |
| 2 (NT) | Little 2-discs: E₂ as base |
| 3 (NS) | Delooping to E₃ |
| ⊕ | ⊗-Day convolution: E_a ⊗ E_b → E_{a+b} |
| ⊗ | Nested factorization integration |
| Depth | Chromatic height |

**Status**: Conceptual model only. No Lean formalization of operad level.

### 3.5 Reading₃ — HoTT

| GRA element | HoTT meaning |
|---|---|
| Grade n | Truncation / homotopy level |
| 2 (NT) | 2-truncation (groupoid level) |
| 3 (NS) | First non-trivial universe level |
| ⊕ | Suspension Σⁿ: additive on grade |
| ⊗ | Smash product ∧ |
| Depth | Cell count in CW-structure |

**Status**: Conceptual model only. The core insight — "gcd(2,3)=1 implies
all positive n-types are suspension-reachable" — is a restatement of
Freudenthal's theorem in GRA language but is not Lean-formalized in this form.

### 3.6 The Level-1 Isomorphism (R₁ ↔ R₄) — Gap 5 Partial Resolution

**Theorem 3.6.1** (Grade Agreement): In both R₁ and R₄, the grade function
takes values in ℕ, and the set of achievable grades is ℕ≥2 ∪ {0}.

**Theorem 3.6.2** (Additive Agreement): Cup-grade addition in R₁ and
path-concatenation length in R₄ both satisfy:
grade(a ⊕ b) = grade(a) + grade(b).

**Theorem 3.6.3** (Depth Agreement): Cup-length in K_{3,2}^{(c=2)} cohomology
= shortest walk length in K_{3,2} graph, both equal ⌈n/3⌉.

These three theorems together constitute the **entry criterion for
GRA Tower Level 1**: R₁ and R₄ are isomorphic as (2,3)-GRA models.

[Lean evidence: cup-length computed in `Cohomology/`, walks in bipartite
graph computable from `BipartiteDecomp/`; explicit iso NOT yet formalized]

---

## Chapter 4 — Structural Invariants

### 4.1 The =1 Trinity

**Theorem 4.1.1** (Trinity): The following three conditions are equivalent
manifestations of a single structural constraint:

1. **det(P) = 1**: The generating transformation preserves volume.
2. **gcd(NT, NS) = 1**: The two generators are coprime.
3. **Frobenius(NT, NS) = 1**: The only unreachable positive grade is 1.

*Proof of equivalence*:
- det(P) = NT·1 − 1·1 = NT − 1 = 2 − 1 = 1. (Direct computation.)
- gcd(2,3) = 1. (Arithmetic fact.)
- Frobenius(2,3) = 2·3 − 2 − 3 = 1. (Sylvester formula.)

These are not "equivalent" in a logical sense (they're different statements
about different objects) but are **structurally coherent**: they all express
"the system is maximally efficient with no waste."

### 4.2 det=1 Across Readings (Gap 1 Extended)

| Reading | det=1 manifestation | Lean evidence |
|---|---|---|
| R₅ (Analysis) | cutHalf∘cutDouble = id (grade 0 = no net change) | ResolutionShift.lean |
| R₁ (Cohomology) | δ² = 0 (coboundary squares to zero = no net cohomology creation) | Cohomology/Delta/ |
| Algebra213 | normSq_mul (multiplicativity = no norm loss) | Algebra213/ |
| Algebra213 | ofInt_inj (injective = no information loss) | Algebra213/ |
| Algebra213 | conj_conj = id (involution = reversible) | Algebra213/ |

### 4.3 Why Exactly Two Generators? (Gap 4 Resolution)

**Argument**: The number of generators = rank of the P-matrix = 2.

P is 2×2 because:
1. **1×1 would be trivial**: det=1 forces P = [[1]], which generates nothing new.
2. **2×2 is the minimum non-trivial**: SL(2,ℤ) is the simplest infinite group
   with rich structure (modular group, hyperbolic geometry, etc.).
3. **3×3 would overdetermine**: A 3×3 matrix with det=1 and all-positive entries
   has 3 generators (g₁, g₂, g₃). By CRT, if all pairwise gcd=1, Frobenius
   numbers are even smaller (F(2,3,5) = 1), but the additional generator
   introduces **redundancy** — the same grades become reachable via multiple
   independent paths, which is information-theoretically wasteful.

**The 213 answer**: Two generators is the **minimum for universal
reachability with no redundancy at low grades**. With (2,3):
- Grade 2: exactly 1 way (a=1, b=0)
- Grade 3: exactly 1 way (a=0, b=1)
- Grade 4: exactly 1 way (a=2, b=0)
- Grade 5: exactly 1 way (a=1, b=1)
- Grade 6: exactly 2 ways (first non-uniqueness)

Adding a third generator would make grade 5 = 2+3 = 5 reachable in 2 ways
already, introducing premature redundancy.

**Formal statement**: (2,3) is the unique coprime pair (g₁,g₂) with g₁ < g₂
that minimizes g₁ + g₂ subject to gcd(g₁,g₂) = 1 and g₁ ≥ 2.

---

## Chapter 5 — GRA Tower and CD Tower Duality

### 5.1 GRA Tower — Precise Level Definitions (Gap 5 Resolution)

**Definition 5.1.1** (GRA Tower Level): Level L is achieved when exactly L
pairwise Reading-isomorphisms have been established.

| Level | What is proven | Entry criterion |
|---|---|---|
| 0 | Nothing — each Reading known independently | (initial state) |
| 1 | R₁ ≅ R₄ as GRA models | Thm 3.6.1 + 3.6.2 + 3.6.3 |
| 2 | Additionally R₂ ≅ R₃ | Suspension = Day convolution at grade level |
| 3 | Additionally R₅ ≅ R₁ (or R₄) | Resolution grade = cochain degree bridge |
| 4 | All ⊕-structures identified | Universal ⊕-functor across all 5 |
| 5 | All ⊗-structures identified | Universal ⊗-functor (hardest: cup ≅ smash ≅ polynomial) |

**Current status**: Level 1 is ~80% complete (all pieces exist in Lean but
the explicit isomorphism statement is not yet a single theorem).
Levels 2–5 are conceptual only.

### 5.2 CD Tower (Review)

The Cayley-Dickson Tower:
```
Level 0: ℤ (all properties)
Level 1: ℤ[i], ℤ[ω] (lose nothing yet — still commutative)
Level 2: Quaternion-like (lose commutativity)
Level 3: Octonion-like (lose associativity)
Level 4: Sedenion-like (lose alternativity — stabilized)
```

### 5.3 Duality Theorem (Informal)

**Conjecture 5.3.1** (Tower Duality): There is a contravariant correspondence:

```
CD Tower Level n (property P lost)  ←→  GRA Tower Level (5−n) (Reading iso gained)
```

Intuition: When a CD level **loses** a property (e.g., commutativity),
the GRA Tower **gains** an identification (the commutativity-free structure
is the same across one more Reading).

**Status**: Conceptual only. No formal proof. The numerical coincidence
(both towers have ~5 levels) is suggestive but not yet rigorous.

---

## Chapter 6 — Number System Unification

### 6.1 The Hierarchy

```
GRA (universal graded structure)
 │
 ├── Grade-0 layer: Int213 (scalars, {±1} fixed point)
 │    └── Q213 (multiplicative quotient of Nat×Nat)
 │
 ├── Grade-axis layer: Real213 (resolution exponent E = grade)
 │    └── SignedCut (grade + binary direction)
 │
 ├── Grade-morphism layer: Modulus (Nat→Nat transition functions)
 │    └── DyadicFSM (finite-state realization)
 │
 └── Grade-extension layer: CD Tower (algebraic doubling)
```

### 6.2 Key Insight: ℤ and ℚ as Twin Quotients

Both emerge from the same pair structure `(Nat213 × Nat213)`:

| Number system | Equivalence relation | GRA interpretation |
|---|---|---|
| ℤ | (a,b) ~ (c,d) iff a+d = b+c | Grade **difference** (additive quotient) |
| ℚ₊ | (a,b) ~ (c,d) iff a·d = b·c | Grade **ratio** (multiplicative quotient) |

This is GRA's ⊕ and ⊗ incarnated as number systems:
- ℤ encodes the ⊕-structure (differences = grade subtraction)
- ℚ encodes the ⊗-structure (ratios = grade division)

[Lean: `NatPairToQPos.lean` for ℚ₊; Int213 for ℤ]

---

## Chapter 7 — Formalizability Assessment

### 7.1 Immediately Formalizable (Lean file can be written today)

| Statement | Estimated complexity | Dependencies |
|---|---|---|
| GRA category definition (Ob, Hom, composition) | Low | Nat arithmetic only |
| minDepth formula proof | Low | Nat.div, Nat.mod |
| Greedy optimality proof | Low | case split on mod 3 |
| (2,3) uniqueness (minimal coprime pair) | Low | gcd, comparison |
| Hom-set cardinality formula | Medium | number of solutions to 2a+3b=k |
| GRA model typeclass | Medium | structure definition |
| R₅ is a GRA model (from ResolutionShift) | Medium | existing ResolutionShift |
| R₁ ≅ R₄ at grade level | Medium-High | needs CupLength + WalkLength |

### 7.2 Requires Conceptual Work First

| Statement | Blocker |
|---|---|
| R₂ ≅ R₃ | No Lean operad formalization |
| Tower Duality | No formal statement yet |
| Adelic GRA | Requires p-adic + real integration |
| det=1 ↔ ModAdjunction triangle | Conceptual bridge unclear |

### 7.3 Proposed Lean Directory Structure

```
lean/E213/Lib/Math/GRA/
├── Core.lean              -- GRACat structure, Ob, Hom, composition
├── Generators.lean        -- NT=2, NS=3, gcd=1, Frobenius=1
├── Depth.lean             -- minDepth, greedy optimality
├── Model.lean             -- GRA model typeclass
├── Reading/
│   ├── Analysis.lean      -- R₅ instance (reuses ResolutionShift)
│   ├── Cohomology.lean    -- R₁ instance (reuses CupLength)
│   └── Graph.lean         -- R₄ instance (walk length)
└── Bridge/
    ├── R1R4Iso.lean       -- Level 1 isomorphism
    └── NumberUnify.lean   -- ℤ/ℚ twin quotient
```

---

## Chapter 8 — Open Frontiers

### 8.1 ℤ-Graded Extension

Can we assign grade(cutDouble) = −1? If so:
- cutDouble ∘ cutHalf = id → grade(-1) + grade(1) = grade(0) ✓
- GRA extends from ℕ-graded to ℤ-graded
- Hom(m,n) becomes non-empty even for m > n (= coarsening maps)
- det=1 means: "grade(+1 path) + grade(-1 path) = 0" always

**Test**: Does `cutDouble` satisfy a ℤ-version of IsResolutionShift?
```
IsResolutionShiftZ cutDouble (-1) := 
  ∀ M E m k, E ≥ 1 → cutDouble (dyadicCut M E) m k = dyadicCut M (E - 1) m k
```

### 8.2 Inter-Reading Translation

The "killer app" for GRA: if R_i ≅ R_j, then every theorem in R_i
has a counterpart in R_j. Example translations to discover:

| Source theorem | Source Reading | Target Reading | Predicted target |
|---|---|---|---|
| Poincaré duality | R₁ | R₅ | Some self-duality of modulus structure? |
| Euler formula V−E+F | R₄ | R₃ | Euler characteristic in HoTT? |
| Weierstrass (generic non-smooth) | R₅ | R₁ | Generic cohomology class is non-cup-decomposable? |
| Koszul duality | R₂ | R₄ | Graph duality? |

### 8.3 The (2,3,5) Extension

Adding d = 5 as a third generator:
- Frobenius(2,3,5) = 1 (same as (2,3) — already universal at ≥2)
- But the **depth spectrum changes**: depth(7) = 2 with (2,5) available,
  vs depth(7) = 3 with only (2,3)
- This could model "dimensional" or "simplicial" degrees beyond (2,3)

### 8.4 Quantum Information Grade

Entanglement as GRA grade:
- 2-qubit entangled state: grade 2
- 3-qubit GHZ: grade 3
- General n-qubit: grade n = 2a + 3b decomposition
- LOCC classification ↔ depth classification?

---

## Appendix A — Notation Summary

| Symbol | Meaning |
|---|---|
| P | [[2,1],[1,1]] ∈ SL(2,ℤ) |
| NT | 2 (temporal generator) |
| NS | 3 (spatial generator) |
| d | 5 = NT + NS (total vertex count) |
| PGen | {n : ∃a,b≥0, 2a+3b = n} = ℕ\{1} |
| minDepth(n) | min(a+b) over 2a+3b=n |
| ⊕ | Grade-additive operation (independent) |
| ⊗ | Grade-submultiplicative operation (interactive) |
| R₁...R₅ | Five Readings of GRA |
| GRA Tower | Progressive identification of Readings |
| CD Tower | Cayley-Dickson property loss tower |

## Appendix B — Lean File Cross-Reference

### B.1 GRA sub-tree (post-Marathon 16, primary)

| Book Section | Lean Module | Content |
|---|---|---|
| Ch.1 (P-matrix, generators 2,3, PGen, depth) | `GRA/GRAModel.lean` | 7-axiom typeclass `GRAModel` + `GRAIso` refl/symm/trans |
| Ch.2 (universal reachability, greedy optimality) | `GRA/NumberTheory.lean` | hub instance `GRA23_NT` on ℕ; `nt_reach`, `nt_greedy`, `nt_depth_eq` |
| Ch.3 R₁ (Cohomology Reading) | `GRA/Cohomology.lean` | `GRA23_Cohomology` + iso to NT |
| Ch.3 R₂ (Higher Algebra Reading) | `GRA/HigherAlgebra.lean` | `GRA23_HigherAlgebra` + universality capstone `gra_universality_witness` |
| Ch.3 R₃ (HoTT Reading) | `GRA/HoTT.lean` | `GRA23_HoTT` + iso to NT |
| Ch.3 R₄ (Graph Reading) | `GRA/Graph.lean` | `GRA23_Graph` + iso to NT |
| Ch.3 R₅ (Analysis Reading) | `GRA/Analysis.lean` | `GRA23_Analysis` + iso to NT |
| Ch.8 (translation programme) | `GRA/Translation.lean` | `graph_distance_implies_cup_length`, `cup_grade_is_resolution_compose`, `master_translation_from_any`, `universal_depth_comparison`, `gra_translation_witness` |

### B.2 Supporting sub-trees (citation back-pointers)

| Book Section | Primary Lean File |
|---|---|
| Ch.1 (PGen, P-orbits) | `Mobius213/Px/` |
| Ch.2 (Composition additivity, resolution shift) | `Analysis/ResolutionShift.lean` |
| Ch.3 R₁ (Cup ring source) | `Cohomology/Cup/`, `Cohomology/Bipartite/` |
| Ch.3 R₄ (BipartiteDecomp source) | `BipartiteDecomp/` |
| Ch.4 (det=1 in Algebra Tower) | `CayleyDickson/` |
| Ch.6 (ℤ/ℚ twins, Adelic) | `NatPairToQPos.lean`, `Padic/` |
| Ch.7 (GradedRing) | `ParadigmDomainGradedRing.lean` |
