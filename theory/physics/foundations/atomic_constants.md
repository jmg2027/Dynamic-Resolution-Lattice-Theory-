# Atomic Constants Uniqueness (C2)

**Status**: Closed via Steps 1-7 (full `∀(m, n)` iff with bounds 2 ≤ m, n).
**Promoted from research-notes**: 2026-05-22.

Pattern 3 (mixed-status, sub-conjecture of chiral cup ring catalog).  Chiral cup ring catalog §C2 statement
+ step log remains in the catalog; the closure proof + narrative are
here.

## Overview

The atomic 4-tuple **(NS, NT, c, d) = (3, 2, 2, 5)** is the unique
integer solution to a small set of self-consistency equations
derivable from 213-Algebra alone, without external input.

The dominant constraint is **C2b**:

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
   `Lib/Math/Extras/CauchySchwarz.two_mul_le_sq_add_sq`).
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

## Research-note provenance

`research-notes/G35_chiral_cup_ring_catalog.md` **§C2** — conjecture
statement + step log (Steps 1-7 closed).  Chiral cup ring catalog itself stays active
(field-level catalog); this chapter is the per-conjecture closure
narrative.

The §0.5 promotion-status section of chiral cup ring catalog tracks this chapter as
the C2 destination.

## Open frontier

C2 is **closed**.  No open work at this conjecture's level.

Adjacent: C2a (uniqueness of `c · m · n = m² + m + n − 2` at c = 2)
and C2c (`d = 5` derivation from `c · m · n` constraint) have
explicit decide checks but no parametric extension yet.  These are
secondary because c = 2 and d = 5 follow from C2b + the
fractal-resolution lift `d^(d²) = N_U` (per `seed/RESOLUTION_LIMIT_SPEC.md`).

## How to verify

```bash
cd lean
lake build E213.Lib.Physics.Foundations
python3 tools/scan_axioms.py Lib/Physics/Foundations
```

## Citation guidance

- ✅ `theory/physics/foundations/atomic_constants.md` (closure narrative)
- ✅ `research-notes/G35_chiral_cup_ring_catalog.md` §C2 (conjecture
  statement + step log within broader catalog)
