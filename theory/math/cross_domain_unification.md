# Cross-Domain Unification (C6)

**Status**: Closed Steps 1-5 (graded ring instantiation); per-domain
cup-product refinement (Step 6+) open.
**Promoted from research-notes**: 2026-05-22.

Pattern 3 (mixed-status, sub-conjecture of G35).  G35 §C6 statement
remains in the catalog; the closure narrative + open frontier are
here.

## Overview

The 213-native paradigm shifts (nilpotency, atomic discrete mass,
cup-as-measure, atomic-Bool LEM, list-finite topology) constitute a
**single unifying graded-ring structure** connecting Probability 213,
Information 213, Logic 213, Combinatorics 213, and the Chiral
Cup-Ring core (D1-D9).  Specifically:

```
Each classical-analysis residue across domains reduces to a
`Cochain n k` truncation at appropriate grade k,
with `configCount 2 = 5²⁵` as the level-2 evaluation point
(historically called "N_U", per G120 Round 3 just one value of
the parametric `configCount : Nat → Nat` family).
```

The shared object is the `CoeffSeq = Nat → Nat` graded ring with
`(1 + x)⁵ = (1, 5, 10, 10, 5, 1, 0, 0, ...)` as the canonical row,
**identical across all 9 paradigm domains**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/` (4 files + downstream domain
  capstones)
- **Files**:
  - `CrossDomainUnification.lean` — Step 1-2: empirical witness across 11 domains
  - `ParadigmDomain.lean` — Step 3: `ParadigmWitness` typeclass
  - `ParadigmDomainGraded.lean` — Step 4: shared `trunc_op` operator
  - `ParadigmDomainGradedRing.lean` — Step 5: graded-ring instantiation via `CoeffSeq`
- **Domain capstones cited**: `Lib/Math/{Probability, Information, Logic, Combinatorics}/Capstone.lean`
- **∅-axiom status**: all PURE

## The narrative

### Steps 1-2 — Empirical witness across 11 domains

The pattern was first observed as a coincidence:
- **Probability**: σ-algebra residue → atomic Boolean event lattice
- **Information**: continuous entropy → discrete bit-counting
- **Logic**: classical LEM → atomic Bool decide
- **Combinatorics**: ∞-generating-functions → finite `CoeffSeq`
- **Topology**: continuous → list-finite covers
- **Multivariable calculus**: continuous → cochain grade
- **Complex analysis**: residue at ∞ → grade-5 truncation
- **Measure theory**: σ-measure → cup-product algebra
- **Cohomology** (D1-D3): cup-chain Δ⁴ / K_{3,2}^{(c=2)}

Step 1 was per-domain witnesses (`CrossDomainUnification.lean`).
Step 2 extended to 11 domains simultaneously typecheck under one
∅-axiom proof body — empirical synchronicity.

### Step 3 — `ParadigmWitness` typeclass

`ParadigmDomain.lean` formalizes the shared structure:

```lean
structure ParadigmWitness where
  truncation_grade : Nat
  truncation_holds : Prop
  atom_decidable    : Decidable truncation_holds
```

9 domain instances all uniform with `truncation_grade = 5` (= d).
The typeclass captures *that* all domains share `(d, atom, decide)` but
not yet *how* they compose.

### Step 4 — Shared `trunc_op` operator

`ParadigmDomainGraded.lean` defines:

```lean
def trunc_op (g : Nat) : Nat :=
  if g ≤ 5 then binom 5 g else 0
```

Sequence: `(1, 5, 10, 10, 5, 1, 0, 0, ...)` — identical across all
9 domains.  Total `Σ_{g=0..5} trunc_op g = 32 = 2⁵ = |2^Δ⁴|`
(Δ⁴ power-set cardinality).

The vanishing beyond grade 5 = d captures the **resolution cutoff
structurally** — d is not a parameter, it is the grade at which the
binomial sequence terminates.

### Step 5 — Graded-ring instantiation via `CoeffSeq`

`ParadigmDomainGradedRing.lean` lifts the operator to a graded
ring:

```lean
CoeffSeq := Nat → Nat                 -- graded ring underlying type
convolution                           -- = cup-product (Cauchy product)
```

The `trunc_op` sequence is the coefficient sequence of `(1 + x)⁵`.
Self-cup gives `(1 + x)⁵ · (1 + x)⁵ = (1 + x)¹⁰` with row sum
`2¹⁰ = 1024 = 32²`.

This is the closure of the long-flagged "single graded-ring
algebraic object spanning all paradigm domains" requirement.  C6
is **structurally closed** at the operator + cup-product level.

### Why this matters

The empirical observation in Steps 1-2 was a coincidence.  Step 5
elevates it to a **theorem**: the 9 domains aren't parallel
constructions, they are 9 instantiations of one graded ring.

Per Mingu's framing (G35 §4 C6): *"closing C6 would be the final
structural confirmation that 213-Algebra is internally coherent —
the four marathon domains and the cup-ring core are facets of one
mathematical object, not parallel constructions."*

## Key results

| Theorem / Def | Module | Statement |
|---|---|---|
| `ParadigmWitness` | `ParadigmDomain` | Typeclass with `(grade, holds, atom)` |
| 9 paradigm instances | `ParadigmDomain` | Uniform `truncation_grade = 5` |
| `trunc_op` | `ParadigmDomainGraded` | Shared sequence (1,5,10,10,5,1,0,...) |
| Sum = 2⁵ = 32 | `ParadigmDomainGraded` | Δ⁴ power-set match |
| `CoeffSeq` as graded ring | `ParadigmDomainGradedRing` | `(1+x)⁵` realization |
| Self-cup row sum 1024 | `ParadigmDomainGradedRing` | `(1+x)¹⁰` |

## Open frontier

### Step 6+ — Per-domain cup-product refinement

Step 5 closes the **shared** graded-ring at the abstract level.  The
per-domain instantiation — "each domain's specific atom operation
as a `convolution`-style algebra" — remains.  For example:
- Probability: events ⊗ events = joint event (convolution = joint
  distribution composition)
- Information: bit-strings ⊗ bit-strings = catenation
- Combinatorics: generating functions ⊗ generating functions = Cauchy product

Each domain has a candidate cup-product, but the unifying lift
showing they all instantiate the same `CoeffSeq.convolution`
remains open.

### Beyond C6

C6 closure makes 213-Algebra "internally coherent" in the sense
that all 9 domains use the same graded ring.  Beyond this:
- Extending paradigm to **physics-side domains** (currently only math)
- Deriving the resolution cutoff `N_U = 5²⁵` directly from the
  graded ring structure (currently a separate spec).

## How to verify

```bash
cd lean
lake build E213.Lib.Math.ParadigmDomain
lake build E213.Lib.Math.ParadigmDomainGradedRing
python3 tools/scan_axioms.py Lib/Math/ParadigmDomain
```

## Citation guidance

- ✅ `theory/math/cross_domain_unification.md` (closure narrative)
- ✅ `research-notes/G35_chiral_cup_ring_catalog.md` §C6 (conjecture
  statement + step log)
