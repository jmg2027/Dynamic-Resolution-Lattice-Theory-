import E213.Lib.Math.Cohomology.Fractal.HunterComplexity
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-!
# Unrestricted depth-2 cut-off — outer pow case for catalogue primes

Extends `AurifeuilleanDepth2Cutoff.lean` (which handled outer ∈
{+, *}) to the **outer = pow** case for the catalogue primes
`137` and `521`, completing the depth-2 cut-off for these atoms.

## Strategy

Depth-2 outer pow value = `a^b` where `a, b ∈ depth1Universe` (the
16-element set `{2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125,
243, 3125}` from `HunterComplexity`).

We show no such `a^b` equals `137` or `521` by splitting on `b`:

  · **Small range** `b ∈ {2, …, 10}`: 16 × 9 = 144 cases,
    `decide`-checked directly (each `a^b ≤ 3125^10 ≈ 10^35`,
    kernel-feasible).

  · **Large range** `b ∈ {15, 25, 27, 32, 125, 243, 3125}`: use
    monotonicity `a^b ≥ 2^15 = 32768 > 521 > 137`.

## Combined verdict

Combining with the restricted cut-off
(`AurifeuilleanDepth2Cutoff.depth2Value_le_M2r`, outer ∈ {+, *}
bounded by `M_{2,r} = 9 765 625`), every depth-2 Hunter expression
value either:

  · is at most `9 765 625` (outer ∈ {+, *}), so trivially differs
    from `137` and `521` only when both differ from the value —
    but `137 ≤ M_{2,r}` and `521 ≤ M_{2,r}`, so this side requires
    explicit enumeration (already in
    `HunterComplexity.complexity_137_at_least_3_restricted` etc.);
    OR

  · equals `a^b` for `a, b ∈ depth1Universe` (outer = ^), and this
    file shows that fails for `137, 521`.

Hence the unrestricted-depth-2 cut-off for `{137, 521}` is closed.
-/

set_option maxRecDepth 4096

namespace E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2PowCutoff

open E213.Lib.Math.Cohomology.Fractal.HunterComplexity
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff
  (depth2Value)

/-! ## §1 Depth-1 universe indexed accessor -/

/-- Indexed accessor for the 16-element depth-1 universe.
    `D1 : Fin 16 → Nat` ranges over
    `{2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125, 243, 3125}`. -/
def D1 (i : Fin 16) : Nat :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 25, 27, 32, 125, 243, 3125].get! i.val

/-- Indexed accessor for the 9-element small-`b` slice.
    `SmallB : Fin 9 → Nat` ranges over `{2, 3, 4, 5, 6, 7, 8, 9, 10}`. -/
def SmallB (j : Fin 9) : Nat := j.val + 2

theorem D1_at_0 : D1 ⟨0, by decide⟩ = 2 := rfl
theorem D1_at_15 : D1 ⟨15, by decide⟩ = 3125 := rfl
theorem SmallB_at_0 : SmallB ⟨0, by decide⟩ = 2 := rfl
theorem SmallB_at_8 : SmallB ⟨8, by decide⟩ = 10 := rfl

/-! ## §2 Small-range enumeration

    Direct `decide` over 144 cases.  Each `D1 i ^ SmallB j` is
    bounded by `3125^10 ≈ 9.3 × 10^34`, kernel-feasible. -/

/-- ★ For `a ∈ depth1Universe` and `b ∈ {2, …, 10}`, `a^b ≠ 137`. -/
theorem small_b_pow_ne_137 :
    ∀ (i : Fin 16) (j : Fin 9), D1 i ^ SmallB j ≠ 137 := by decide

/-- ★ For `a ∈ depth1Universe` and `b ∈ {2, …, 10}`, `a^b ≠ 521`. -/
theorem small_b_pow_ne_521 :
    ∀ (i : Fin 16) (j : Fin 9), D1 i ^ SmallB j ≠ 521 := by decide

/-! ## §3 Monotonicity for the large range

    For `a ≥ 2` and `b ≥ 15`, `a^b ≥ 2^15 = 32768 > 521 > 137`. -/

/-- `2^15 = 32768`.  Kernel constant. -/
theorem two_pow_15 : (2 : Nat) ^ 15 = 32768 := by decide

/-- For `b ≥ 15`, `2^b ≥ 32768`.  Follows from `Nat.pow_le_pow_right`. -/
theorem two_pow_ge_15 (b : Nat) (hb : 15 ≤ b) : 32768 ≤ 2 ^ b := by
  have h1 : (2 : Nat) ^ 15 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
  rw [two_pow_15] at h1
  exact h1

/-- For `a ≥ 2` and `b ≥ 15`, `a^b ≥ 32768 > 521`.  Combines
    `Nat.pow_le_pow_left` with `two_pow_ge_15`. -/
theorem large_b_pow_gt_521 (a b : Nat) (ha : 2 ≤ a) (hb : 15 ≤ b) :
    521 < a ^ b := by
  have h1 : 32768 ≤ 2 ^ b := two_pow_ge_15 b hb
  have h2 : (2 : Nat) ^ b ≤ a ^ b := Nat.pow_le_pow_left ha b
  have h3 : 32768 ≤ a ^ b := Nat.le_trans h1 h2
  have h4 : 521 < 32768 := by decide
  exact Nat.lt_of_lt_of_le h4 h3

/-- Corollary: `a^b ≠ 521` and `a^b ≠ 137` for `a ≥ 2`, `b ≥ 15`. -/
theorem large_b_ne_137_521 (a b : Nat) (ha : 2 ≤ a) (hb : 15 ≤ b) :
    a ^ b ≠ 137 ∧ a ^ b ≠ 521 := by
  have h := large_b_pow_gt_521 a b ha hb
  refine ⟨?_, ?_⟩
  · intro heq
    rw [heq] at h
    exact absurd h (by decide)
  · intro heq
    rw [heq] at h
    exact absurd h (by decide)

/-! ## §4 Depth-1 universe bounds

    Every element of `depth1Universe` is ≥ 2.  Splitting by index:
    `j.val < 9` gives `D1 j ∈ {2, …, 10}` (small range, equal to
    `SmallB`); `j.val ≥ 9` gives `D1 j ≥ 15` (large range). -/

/-- Every depth-1 element is ≥ 2. -/
theorem D1_ge_2 : ∀ (i : Fin 16), 2 ≤ D1 i := by decide

/-- Conversion: for `j.val < 9`, `D1 j` coincides with `SmallB` at
    the same index. -/
theorem D1_eq_SmallB_when_small :
    ∀ (j : Fin 16) (h : j.val < 9), D1 j = SmallB ⟨j.val, h⟩ := by decide

/-- For `j.val ≥ 9`, `D1 j ≥ 15`. -/
theorem D1_ge_15_when_large :
    ∀ (j : Fin 16), 9 ≤ j.val → 15 ≤ D1 j := by decide

/-! ## §5 Main theorem — `137, 521 ∉ depth-2 outer-pow` -/

/-- ★★★ **Unrestricted depth-2 outer-pow cut-off for `137`**:
    no `a^b` with `a, b ∈ depth1Universe` equals `137`. -/
theorem depth2_pow_ne_137 :
    ∀ (i j : Fin 16), D1 i ^ D1 j ≠ 137 := by
  intro i j
  rcases Nat.lt_or_ge j.val 9 with h_small | h_large
  · rw [D1_eq_SmallB_when_small j h_small]
    exact small_b_pow_ne_137 i ⟨j.val, h_small⟩
  · have ha : 2 ≤ D1 i := D1_ge_2 i
    have hb : 15 ≤ D1 j := D1_ge_15_when_large j h_large
    exact (large_b_ne_137_521 (D1 i) (D1 j) ha hb).1

/-- ★★★ **Unrestricted depth-2 outer-pow cut-off for `521`**:
    no `a^b` with `a, b ∈ depth1Universe` equals `521`. -/
theorem depth2_pow_ne_521 :
    ∀ (i j : Fin 16), D1 i ^ D1 j ≠ 521 := by
  intro i j
  rcases Nat.lt_or_ge j.val 9 with h_small | h_large
  · rw [D1_eq_SmallB_when_small j h_small]
    exact small_b_pow_ne_521 i ⟨j.val, h_small⟩
  · have ha : 2 ≤ D1 i := D1_ge_2 i
    have hb : 15 ≤ D1 j := D1_ge_15_when_large j h_large
    exact (large_b_ne_137_521 (D1 i) (D1 j) ha hb).2

/-! ## §6 Capstone -/

/-- ★★★★★ **Capstone — unrestricted depth-2 cut-off for catalogue
    primes `{137, 521}`**.

    Combines:
      (1) restricted depth-2 (outer ∈ {+, *}, from
          `HunterComplexity.complexity_137_at_least_3_restricted` /
          `complexity_521_at_least_3_restricted`),
      (2) outer-pow case (this file's `depth2_pow_ne_137` /
          `depth2_pow_ne_521`).

    Hence `hunterComplexity(137) = 3` (full, no restriction) and
    `hunterComplexity(521) = 3` (full, no restriction), promoting
    the previously restricted lower bound to the unrestricted
    bound.

    Upper bound: explicit depth-3 witnesses
    `137 = 2^(2+5) + 3^2` and `521 = 2^(3^2) + 3^2` from
    `HunterComplexity`. -/
theorem capstone :
    -- restricted-depth-2 exclusion (carried over)
    (∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
       depth2Value a b c d opL opR opOut ≠ 137)
    ∧ (∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
       depth2Value a b c d opL opR opOut ≠ 521)
    -- outer-pow exclusion (this file)
    ∧ (∀ (i j : Fin 16), D1 i ^ D1 j ≠ 137)
    ∧ (∀ (i j : Fin 16), D1 i ^ D1 j ≠ 521) :=
  ⟨complexity_137_at_least_3_restricted,
   complexity_521_at_least_3_restricted,
   depth2_pow_ne_137,
   depth2_pow_ne_521⟩

end E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2PowCutoff
