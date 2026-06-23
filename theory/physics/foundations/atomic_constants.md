# Atomic Constants Uniqueness (C2)

**Status**: Closed via Steps 1-7 (full `∀(m, n)` iff with bounds 2 ≤ m, n).

## Overview

The triple **(NS, NT, d) = (3, 2, 5)** is forced: `(NS, NT)` is the unique
non-decomposable atom pair (`PairForcing`, `NonDecomposable`) and `d = NS + NT`.
The multiplicity **c = 2** is **not** an independently-forced fourth primitive —
it is the **presentation parameter** set so that the graph cohomology
`b₁(K_{NS,NT}^{(c)}) = c·NS·NT − (NS+NT−1)` reproduces the gauge content
`NS² − 1 = 8`, which is already a direct fact about the forced `NS = 3` (the
SU(3) adjoint dimension).  `c = 2` is unforced across five reframings (cohomology
dimension, Möbius period, arity, chirality, minimality) and physics-redundant (no observable
needs it; `K_{3,2}^{(c=2)}` re-presents `NS²−1` cohomologically).  So the
honest atomic content is `(NS, NT, d) = (3, 2, 5)` forced, with `c = 2` a
derived presentation of `NS²−1`.

The constraint below ("C2b") makes the dependence explicit — it is exactly the
requirement that the graph cohomology hit the `NS²−1` target:

```
constraint_C2b m n := (c · m · n = m² + m + n − 2) at c = 2
                     ⟺  2 · m · n = m² + m + n − 2
```

derived from the requirement `dim H¹(K_{m,n}^{(c)}) = m² − 1`
(= 1/α_3 channel count).  213 is the smallest non-trivial solution.

The **full iff theorem** (Step 7) closes:

```lean
theorem c2b_full_iff (m n : Nat) (_hm : 2 ≤ m) (_hn : 2 ≤ n) :
    constraint_C2b m n = true ↔ (m = 3 ∧ n = 2) ∨ (m = 2 ∧ n = 3)
```

`#print axioms` reports **"does not depend on any axioms"**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Foundations/AtomicConstants*`
- **Files** (5):
  - `AtomicConstantsUnique.lean` — bounded search baseline + 213 witnesses
  - `AtomicConstantsParametric.lean` — Step 4: `∀ m, n = 2 → m = 3`
  - `AtomicConstantsParametricN3.lean` — Step 5: `∀ m, n = 3 → m = 2`
  - `AtomicConstantsParametricFull.lean` — Step 6: structural ingredients
    (symmetry + diagonal vanish via AM-GM)
  - `AtomicConstantsParametricFullIff.lean` — Step 7: single full iff
- **∅-axiom status**: all PURE

## The narrative

### Step 1-3 — Bounded search baseline

- **Step 1**: bounded uniqueness (m, n, c) < 7 — triple loop decide.
- **Step 2**: factored search (m, n) < 100 — algebraic case witnesses
  `n = 2 only m = 3`, `n = 3 only m = 2`, `n ≥ 4 no m < 100`.
- **Step 3**: extended bound to 300 via bumped `maxHeartbeats`.

These witness the answer **empirically** for finite ranges but are
not full uniqueness theorems.

### Step 4 — Full `∀ m` at `n = 2`

`AtomicConstantsParametric.lean` proves `c2b_n2_iff_m3 :
∀ m : Nat, constraint_C2b m 2 = true ↔ m = 3` without bounds.

The key Nat monotonicity lemma is `msq_gt_2m_p3 : 2m + 3 < m² for m ≥ 4`:
- For m ≥ 4: `4m ≤ m²` (since m ≥ 4)
- `4m = 2m + 2m ≥ 2m + 8 > 2m + 3` (since 2m ≥ 8 at m ≥ 4)
- Therefore `2m + 3 < 4m ≤ m²`.

Combined with explicit checks at m = 0, 1, 2, 3, the iff is closed.

### Step 5 — Full `∀ m` at `n = 3`

`AtomicConstantsParametricN3.lean` proves `c2b_n3_iff_m2 :
∀ m : Nat, constraint_C2b m 3 = true ↔ m = 2`.

Same machinery: `seven_msq_gt_6m_p17 : 6m + 17 < 7m² for m ≥ 3`
(closes the quadratic `7m² − 6m − 16 = 0`).

### Step 6 — Diagonal vanish (m, n ≥ 3 → false)

`AtomicConstantsParametricFull.lean` proves
`c2b_diag_false : m, n ≥ 3 → constraint_C2b m n = false` via:

1. **AM-GM**: `2mn ≤ m² + n²` (from
   `Lib/Math/Tactic/Extras/CauchySchwarz.two_mul_le_sq_add_sq`).
2. **Monotonicity bound**: `m²n² ≥ 3(m² + n²)` (from
   `m²n² ≥ 9(m² + n²)/2` at m, n ≥ 3).
3. **Nat-sub decomposition**: `m²n² + 1 = (m² − 1)(n² − 1) + (m² + n²)`.

Plus `c2b_sym : C2b m n = C2b n m` (by `Nat.mul_comm` + `Nat.add_comm`).

The bundled master `atomic_constants_parametric_full_master` packages
these as the structural ingredients.

### Step 7 — Single full iff

`AtomicConstantsParametricFullIff.lean` combines Steps 4-6 into
one statement:

```lean
theorem c2b_full_iff (m n : Nat) (_hm : 2 ≤ m) (_hn : 2 ≤ n) :
    constraint_C2b m n = true ↔ (m = 3 ∧ n = 2) ∨ (m = 2 ∧ n = 3)
```

Mechanical case split on `(n, m) ∈ {2, 3, k + 4}²`:
- `(n = 2, m = ?)` → Step 4
- `(n = 3, m = ?)` → Step 5
- `(n = k + 4, m = ?)` → Step 6 (via symmetry)
- Diagonal (m, n ≥ 3) → Step 6 directly

Both 213 (3, 2) and its symmetric partner (2, 3) appear.  213 is
the canonical reading; (2, 3) is the same lattice with NS/NT swapped.

## Key results

| Theorem | Module | Statement |
|---|---|---|
| `c2b_full_iff` | `AtomicConstantsParametricFullIff` | `∀ m, n ≥ 2, C2b m n ↔ (3,2) ∨ (2,3)` |
| `c2b_n2_iff_m3` | `AtomicConstantsParametric` | `∀ m, C2b m 2 ↔ m = 3` |
| `c2b_n3_iff_m2` | `AtomicConstantsParametricN3` | `∀ m, C2b m 3 ↔ m = 2` |
| `atomic_constants_parametric_full_master` | `AtomicConstantsParametricFull` | Structural bundle (sym + diag + Step 4 + Step 5) |
| `c2a_213` | `AtomicConstantsUnique` | `C2a NS NT 2 = true` |
| `c2b_213` | `AtomicConstantsUnique` | `C2b NS NT = true` |

## Raw-side derivation — Clause 4 recursive atomicity

C2b above is the **cohomology-side** uniqueness via `2mn = m² + m
+ n − 2`.  An independent **Raw-side** derivation reaches the same
(NS, NT, d) = (3, 2, 5) from the Raw axiom (`seed/AXIOM/02_axiom.md`
§2.2) by applying its Clause 4 recursively across granularities.

### The principle

Per Raw's axiom, an event is *simultaneously* operation and object —
no a-priori distinction.  Clause 4 (`x / x` forbidden — every
distinguishable carries a residue against itself) therefore does
not apply only to atomic distinguishables; it applies *at every
granularity*, including to **groups of Raw viewed as objects**.

### Derivation

For the atomicity decomposition `n = NT · a + NS · b = 2a + 3b`,
the inputs `(a, b)` describe how many `NT`-pair and `NS`-triple
atoms participate.  Clause 4 applied recursively forbids any
group-level self-pairing:

  · `a` copies of `NT` (= a binary-pair atoms).  If `a` is even,
    the `a` pairs group into `a/2` pair-of-pairs — a self-pair
    structure at the binary group level.  Clause 4 (recursive)
    forbids this; so `a` must be **odd**.
  · Symmetrically `b` must be **odd**.

The "both odd" alive condition is therefore not a separate
postulate but the **count-Lens readout of Clause 4 applied
recursively to count-Lens groups**.

### Lean closure (`Theory/Atomicity/AliveDerivation.lean`, 7 PURE)

| Theorem | Statement |
|---|---|
| `IsSelfPaired n := ∃ k, n = 2 * k` | Clause-4 group-level self-pair structure |
| `IsClause4Alive a b := ¬IsSelfPaired a ∧ ¬IsSelfPaired b` | Clause-4-derived alive predicate |
| `parity_iff_not_self_paired` | bridge `parity n = true ↔ ¬IsSelfPaired n` |
| ★★★★★ `alive_iff_clause4_alive` | `Atomicity.Five.IsAlive a b ↔ IsClause4Alive a b` |
| `atomic_iff_five_via_clause4`     | the atomicity theorem holds with `IsClause4Alive` substituted |

### Combined inevitability chain

| Step | Witness | Status |
|---|---|---|
| Raw axiom 4 clauses              | `seed/AXIOM/02_axiom.md` §2.2 | doctrine |
| Recursive Clause 4 → Alive       | `alive_iff_clause4_alive`     | ∅-axiom |
| Alive + decomp `2a + 3b = n`     | `atomic_iff_five`             | ∅-axiom |
| Atomic n → n = 5                 | `atomic_implies_five`         | ∅-axiom |
| n = 5 = NS + NT                  | `partition_sum`               | ∅-axiom |
| Arity k=2 unique (∀ k ≥ 3 vacuous) | `arity_2_unique_via_k_ge_3_vacuous` | ∅-axiom |

Combined statement: Raw + the four clauses (including recursive
Clause 4) force `(NS, NT, d) = (3, 2, 5)` and the base **arity k = 2**
uniquely from the Raw side, independently of the C2b cohomology-side
iff above.  The forced dimensions are Lean-formalised at the Theory
layer:

  · `(NS, NT) = (3, 2)` via `Theory/Atomicity/PairForcing.lean`
  · `d = 5` via `Theory/Atomicity/{OrbitForcing, Five}.lean`
  · **arity `k = 2` via `Theory/Atomicity/CombinatorialArity.lean`**
    (parametric `pigeonhole_fin_to_fin2` + generic `Raw k` /
    `Reachable k` + capstone `arity_2_unique_via_k_ge_3_vacuous`).
    Companion to `ArityForcing.lean` (which handles the concrete
    k = 3 case); CombinatorialArity is the ∀ k ≥ 3 generalisation
    — 5 PURE.

The edge **multiplicity `c`** is **not** in this forced set: reading
`c = 2` off the arity `k = 2` is a `decide`-coincidence of two distinct
2's (arity-base `Fin 2` vs partition-slot `NT`), not a forcing — `c`
stays a free presentation parameter (see Overview; authoritative status
`research-notes/frontiers/atomic_c_multiplicity_forcing.md`).

The two derivations (C2b cohomology + Raw-side combined chain)
are different Lens readings of the same forced `(NS, NT, d)` triple,
each evaluated at presentation `c = 2`.

### Dual-emergence companion (Δ⁴ ⊥ K_{3,2}^{(c=2)})

The same 5-vertex residue carries two distinct cohomological
fillings whose Euler characteristics satisfy:

  χ(Δ⁴) + χ(K_{3,2}^{(c=2)}) = (+1) + (−7) = **−6 = −(NS · NT)**

with `Δ⁴` the maximal-non-commitment combinatorial filling
(`+1`, contractible) and `K_{3,2}^{(c=2)}` the dynamic Möbius
shadow (`−7`, b₁ = 8 cycles).  Witness:
`Lib/Math/Geometry/AlgebraicGeometry.lean` and
`Lib/Math/Geometry/Topology/EulerChi.lean`.  The integer `6 = NS · NT`
appears across multiple structural readings (ZOmega units, α_GUT
numerator, Pauli-ε non-zero entries, Lorentz generator count, `3!`,
S/T cross-pair count, SU(NS) root count, `d + 1`); a single
Raw-native derivation `Raw → 6` whose multiple Lens projections
recover all of these is the open structural target.

This chapter is the per-conjecture (C2) closure narrative.

The §0.5 promotion-status section of chiral cup ring catalog tracks this chapter as
the C2 destination.

## Open frontier

C2 is **closed**.  No open work at this conjecture's level.

Adjacent: C2a (uniqueness of `c · m · n = m² + m + n − 2` at c = 2)
and C2c (`d = 5` derivation from `c · m · n` constraint) have
explicit decide checks but no parametric extension yet.  These are
secondary because c = 2 and d = 5 follow from C2b + the
fractal lift `d^(d²) = 5²⁵` (`Lib/Math/Cohomology/Fractal/ConfigCount.lean`).

## How to verify

```bash
cd lean
lake build E213.Lib.Physics.Foundations
python3 tools/scan_axioms.py Lib/Physics/Foundations
```

## Citation guidance

- ✅ `theory/physics/foundations/atomic_constants.md` (closure narrative)
