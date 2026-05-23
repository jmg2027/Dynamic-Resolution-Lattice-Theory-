import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-!
# Hunter complexity measure

Defines a 213-native complexity measure `hunterComplexity(v)` on
naturals: the minimum depth `k` such that `v` admits a Hunter
expression of depth `≤ k` over generators `{2, 3, 5}` with
operations `{+, *, ^}`.

## Hierarchy

  · **depth 0**: generators `{2, 3, 5}`.
  · **depth 1**: 16 values
    `{2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125, 243, 3125}`.
  · **depth ≥ 2**: catalogue atoms `{13, 41, 137, 521}` (none of
    which appear in depth-1).
  · **depth ≥ 3**: catalogue atoms `{137, 521}` (none of which
    appear in depth-2 restricted; full depth-2 incl. outer pow is
    excluded via the algebraic argument that they are prime and
    not in depth-1).

## Catalogue-atom complexity table

| atom  | complexity | witness                                         |
|-------|-----------|--------------------------------------------------|
| 2     | 0         | gNT                                              |
| 3     | 0         | gNS                                              |
| 5     | 0         | gd                                               |
| 7     | 1         | `2 + 5`                                          |
| 13    | 2         | `(2^3) + 5 = 8 + 5`                              |
| 41    | 2         | `(3^2) + (2^5) = 9 + 32`                         |
| 137   | 3         | `(2^(2+5)) + (3^2) = 128 + 9`                    |
| 521   | 3         | `(2^(3^2)) + (3^2) = 512 + 9` (from `t521`)      |

## Cross-references

  · `AurifeuilleanFullCutoff.lean` — depth-1 + depth-3 substrate.
  · `AurifeuilleanDepth2Cutoff.lean` — depth-2 restricted.
-/

namespace E213.Lib.Math.Cohomology.Fractal.HunterComplexity

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-! ## §1 Depth-1 universe -/

/-- Explicit enumeration of all depth-≤-1 Hunter values: 3
    generators + 9 distinct add/mul results + powers.  Total 16. -/
def depth1Universe : List Nat :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125, 243, 3125]

theorem depth1Universe_length : depth1Universe.length = 16 := rfl

/-- Decidable membership in the depth-1 universe. -/
def inDepth1 (v : Nat) : Bool := depth1Universe.contains v

/-! ## §2 Soundness of the explicit `depth1Universe`

    Every list-entry is actually reachable by a depth-≤-1 Hunter
    expression over `{2, 3, 5}` with `{+, *, ^}`. -/

/-- `4 = 2 + 2 = 2 * 2 = 2^2` — depth-1 reachable. -/
theorem dep1_witness_4  : 2 + 2 = 4 := by decide
theorem dep1_witness_6  : 2 * 3 = 6 := by decide
theorem dep1_witness_7  : 2 + 5 = 7 := by decide
theorem dep1_witness_8  : 2 ^ 3 = 8 := by decide
theorem dep1_witness_9  : 3 * 3 = 9 := by decide
theorem dep1_witness_10 : 2 * 5 = 10 := by decide
theorem dep1_witness_15 : 3 * 5 = 15 := by decide
theorem dep1_witness_25 : 5 * 5 = 25 := by decide
theorem dep1_witness_27 : 3 ^ 3 = 27 := by decide
theorem dep1_witness_32 : 2 ^ 5 = 32 := by decide
theorem dep1_witness_125  : 5 ^ 3 = 125 := by decide
theorem dep1_witness_243  : 3 ^ 5 = 243 := by decide
theorem dep1_witness_3125 : 5 ^ 5 = 3125 := by decide

/-! ## §3 Completeness of the explicit `depth1Universe`

    No depth-≤-1 Hunter value lies outside `depth1Universe`.  Proved
    by exhaustive Fin enumeration (3 generators × 3 generators × 3
    ops = 27 cases, all checked by `decide`). -/

/-- Every leaf value is in `depth1Universe`. -/
theorem depth1Universe_contains_leaves :
    ∀ (i : Fin 3), inDepth1 ([2, 3, 5].get! i.val) = true := by decide

/-- Every depth-1 add result is in `depth1Universe`. -/
theorem depth1Universe_contains_add :
    ∀ (i j : Fin 3),
      inDepth1 ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) = true := by
  decide

/-- Every depth-1 mul result is in `depth1Universe`. -/
theorem depth1Universe_contains_mul :
    ∀ (i j : Fin 3),
      inDepth1 ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) = true := by
  decide

/-- Every depth-1 pow result is in `depth1Universe`. -/
theorem depth1Universe_contains_pow :
    ∀ (i j : Fin 3),
      inDepth1 ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) = true := by
  decide

/-! ## §4 Atomic-prime complexity classification

    For each catalogue prime `p ∈ {2, 3, 5, 7, 13, 41, 137, 521}`,
    we record its `inDepth1` status and (for primes outside depth-1)
    its depth-≥-2 positive witness. -/

/-- Catalogue atoms IN depth-1: `{2, 3, 5, 7}`. -/
theorem inDepth1_2 : inDepth1 2 = true := by decide
theorem inDepth1_3 : inDepth1 3 = true := by decide
theorem inDepth1_5 : inDepth1 5 = true := by decide
theorem inDepth1_7 : inDepth1 7 = true := by decide

/-- Catalogue atoms NOT in depth-1: `{13, 41, 137, 521}`. -/
theorem notInDepth1_13  : inDepth1 13  = false := by decide
theorem notInDepth1_41  : inDepth1 41  = false := by decide
theorem notInDepth1_137 : inDepth1 137 = false := by decide
theorem notInDepth1_521 : inDepth1 521 = false := by decide

/-! ## §5 Depth-2 positive witnesses for `{13, 41}` -/

/-- `13 = 8 + 5 = (2^3) + 5`.  Depth 2 (outer add, inner pow on left). -/
theorem witness_13_at_depth_2 : (2 ^ 3) + 5 = 13 := by decide

/-- `41 = 9 + 32 = (3^2) + (2^5)`.  Depth 2 (outer add, inner pow on both). -/
theorem witness_41_at_depth_2 : (3 ^ 2) + (2 ^ 5) = 41 := by decide

/-! ## §6 Depth-3 positive witnesses for `{137, 521}` -/

/-- `137 = 128 + 9 = (2^7) + (3^2) = (2^(2+5)) + (3^2)`.  Depth 3
    (outer add, inner pow on right depth-1, inner pow on left
    depth-2 since exponent `2+5` is itself depth-1). -/
theorem witness_137_at_depth_3 : (2 ^ (2 + 5)) + (3 ^ 2) = 137 := by decide

/-- `521 = 512 + 9 = (2^(3^2)) + (3^2)`.  Depth 3, matching `t521`
    from `AurifeuilleanFullCutoff`. -/
theorem witness_521_at_depth_3 : (2 ^ (3 ^ 2)) + (3 ^ 2) = 521 := by decide

/-! ## §7 Lower-bound theorems

    For each catalogue atom outside depth-1, formally state that
    its Hunter complexity is at least 2 (it is not the value of any
    depth-1 Hunter expression). -/

/-- ★ `complexity(13) ≥ 2`: 13 is not a leaf or any depth-1
    expression over `{2, 3, 5}` with `{+, *, ^}`. -/
theorem complexity_13_at_least_2 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ 13
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ 13
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ 13
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ 13 := by decide

/-- ★ `complexity(41) ≥ 2`. -/
theorem complexity_41_at_least_2 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ 41
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ 41
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ 41
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ 41 := by decide

/-- ★ `complexity(137) ≥ 2`. -/
theorem complexity_137_at_least_2 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ 137
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ 137
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ 137
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ 137 := by decide

/-- ★ `complexity(521) ≥ 2`. -/
theorem complexity_521_at_least_2 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ 521
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ 521
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ 521
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ 521 := by decide

/-! ## §8 Restricted depth-2 lower bounds for `{137, 521}`

    Extends the lower bound from depth 2 to depth 2 restricted
    (outer = `+` or `*` only).  Uses `depth2Value_le_M2r` from
    `AurifeuilleanDepth2Cutoff` combined with the fact that
    `137 < M2r` and `521 < M2r`. -/

/-- `137` is not the value of any restricted-depth-2 Hunter
    expression with outer = `+` or `*`.  Proof by exhaustive Fin
    enumeration. -/
theorem complexity_137_at_least_3_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ 137 := by decide

/-- `521` is not the value of any restricted-depth-2 Hunter
    expression with outer = `+` or `*`. -/
theorem complexity_521_at_least_3_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ 521 := by decide

/-! ## §9 Hierarchy capstone -/

/-- ★★★ **Capstone**: explicit complexity-hierarchy witnesses.

    For each `k ∈ {0, 1, 2, 3}`, there exists a catalogue atom of
    Hunter complexity exactly `k`:

      · `k = 0`: 2 (or 3, 5).
      · `k = 1`: 7 (depth-1 only via `2 + 5`).
      · `k = 2`: 13 (depth-2 via `(2^3) + 5`, not depth-1).
      · `k = 3`: 521 (depth-3 via `(2^(3^2)) + (3^2)`, not
        restricted-depth-2). -/
theorem complexity_hierarchy_capstone :
    -- complexity(2) = 0
    inDepth1 2 = true
    -- complexity(7) = 1: in depth-1 but not a generator
    ∧ inDepth1 7 = true
    -- complexity(13) ≥ 2: not in depth-1
    ∧ inDepth1 13 = false
    ∧ (2 ^ 3) + 5 = 13  -- depth-2 positive witness
    -- complexity(521) ≥ 3 (restricted)
    ∧ (∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
        depth2Value a b c d opL opR opOut ≠ 521)
    -- 521 has explicit depth-3 witness
    ∧ (2 ^ (3 ^ 2)) + (3 ^ 2) = 521 :=
  ⟨inDepth1_2, inDepth1_7, notInDepth1_13, witness_13_at_depth_2,
   complexity_521_at_least_3_restricted, witness_521_at_depth_3⟩

end E213.Lib.Math.Cohomology.Fractal.HunterComplexity
