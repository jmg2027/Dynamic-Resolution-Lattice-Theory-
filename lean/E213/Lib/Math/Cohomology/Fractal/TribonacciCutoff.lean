import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-!
# Tribonacci-sequence cardinality cut-off

Fifth external sequence in the cut-off applications family.
Tribonacci numbers `T_n` with `T_0 = 0`, `T_1 = 0`, `T_2 = 1`,
`T_{n+3} = T_{n+2} + T_{n+1} + T_n`.

`T_n` grows as `ψ^n` where `ψ ≈ 1.839` is the tribonacci constant
(real root of `x³ = x² + x + 1`).

## Catalogue coincidences

| n | T_n | catalogue role          |
|---|-----|-------------------------|
| 4 | 2   | NT (generator)          |
| 6 | 7   | catalogue prime         |
| 7 | 13  | catalogue prime         |

## Near-boundary phenomenon

★ **`T_16 = 3136` is exactly `11` above `M_1 = 3125`**.  The
Tribonacci sequence threads the depth-1 cut-off boundary unusually
tightly:

  · `T_14 = 927`
  · `T_15 = 1705`
  · **`T_16 = 3136`** ← just 11 above `M_1 = 5^5 = 3125`
  · `T_17 = 5768`

For comparison: Pell, Lucas, Fibonacci all leap past `3125` by
multiple thousands at the cut-off boundary.  Tribonacci's
slower growth rate produces this near-miss.

## Cut-off slices

  · **Depth 1 (M_1 = 3125)**: cut-off at `n ≥ 16` (`T_15 = 1705
    < 3125 < 3136 = T_16`).  The tightest boundary in the
    applications family.
  · **Depth 2 restricted (M_{2,r} = 9 765 625)**: cut-off at
    `n ≥ 30` (`T_29 = 8 646 064 < M_{2,r} < 15 902 591 = T_30`).

## Cross-references

  · `cardinality_cutoff_applications.md` — applications family.
  · `PellCutoff.lean`, `LucasCutoff.lean`, `FibonacciCutoff.lean`
    — sister sequence files.
-/

namespace E213.Lib.Math.Cohomology.Fractal.TribonacciCutoff

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff (M2r depth2Value
  asymptotic_cutoff_at_depth_2_restricted)

/-! ## §1 Tribonacci sequence -/

/-- Tribonacci sequence: `T_0 = 0`, `T_1 = 0`, `T_2 = 1`,
    `T_{n+3} = T_{n+2} + T_{n+1} + T_n`. -/
def Trib : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => Trib (n + 2) + Trib (n + 1) + Trib n

/-! ## §2 Small-value table -/

theorem Trib_0  : Trib 0  = 0 := rfl
theorem Trib_1  : Trib 1  = 0 := rfl
theorem Trib_2  : Trib 2  = 1 := rfl
theorem Trib_3  : Trib 3  = 1 := by decide
theorem Trib_4  : Trib 4  = 2 := by decide
theorem Trib_5  : Trib 5  = 4 := by decide
theorem Trib_6  : Trib 6  = 7 := by decide
theorem Trib_7  : Trib 7  = 13 := by decide
theorem Trib_8  : Trib 8  = 24 := by decide
theorem Trib_14 : Trib 14 = 927 := by decide
theorem Trib_15 : Trib 15 = 1705 := by decide
theorem Trib_16 : Trib 16 = 3136 := by decide
theorem Trib_17 : Trib 17 = 5768 := by decide
theorem Trib_29 : Trib 29 = 8646064 := by decide
theorem Trib_30 : Trib 30 = 15902591 := by decide

/-! ## §3 Catalogue coincidences -/

/-- `T_4 = 2 = NT`. -/
theorem Trib_4_eq_NT : Trib 4 = 2 := Trib_4

/-- `T_6 = 7` (catalogue prime). -/
theorem Trib_6_eq_7 : Trib 6 = 7 := Trib_6

/-- `T_7 = 13` (catalogue prime). -/
theorem Trib_7_eq_13 : Trib 7 = 13 := Trib_7

/-! ## §4 Tight near-boundary at depth-1

    ★ **`T_16 − M_1 = 3136 − 3125 = 11`**: Tribonacci threads the
    depth-1 cut-off boundary tighter than any other sequence in
    the family. -/

theorem Trib_15_below_M1 : Trib 15 < 3125 := by decide
theorem Trib_16_above_M1 : 3125 < Trib 16 := by decide

/-- ★ **Tight near-boundary**: `T_16 − M_1 = 11`. -/
theorem Trib_16_minus_M1_is_11 : Trib 16 - 3125 = 11 := by decide

/-! ## §5 Depth-1 cut-off application -/

theorem Trib_16_exceeds_depth_1 : 3125 < Trib 16 := Trib_16_above_M1

theorem Trib_16_not_at_depth_1 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ Trib 16
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ Trib 16
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ Trib 16
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ Trib 16 :=
  fun i j => asymptotic_cutoff_at_depth_1 (Trib 16) i j Trib_16_above_M1

/-! ## §6 Depth-2-restricted cut-off application -/

theorem Trib_29_below_M2r : Trib 29 < M2r := by decide
theorem Trib_30_above_M2r : M2r < Trib 30 := by decide

theorem Trib_30_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ Trib 30 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted (Trib 30)
      Trib_30_above_M2r a b c d opL opR opOut

/-! ## §7 Capstone -/

/-- ★★★ **Capstone**: Tribonacci catalogue intersections + tight
    near-boundary at depth-1 + cut-off applications. -/
theorem capstone :
    -- Catalogue hits at small index
    Trib 4 = 2 ∧ Trib 6 = 7 ∧ Trib 7 = 13
    -- Tight near-boundary: T_16 just 11 above M_1
    ∧ Trib 16 - 3125 = 11
    -- Depth-1 cut-off boundary
    ∧ 3125 < Trib 16
    -- Depth-2-restricted cut-off boundary
    ∧ M2r < Trib 30 :=
  ⟨Trib_4, Trib_6, Trib_7, Trib_16_minus_M1_is_11,
   Trib_16_above_M1, Trib_30_above_M2r⟩

end E213.Lib.Math.Cohomology.Fractal.TribonacciCutoff
