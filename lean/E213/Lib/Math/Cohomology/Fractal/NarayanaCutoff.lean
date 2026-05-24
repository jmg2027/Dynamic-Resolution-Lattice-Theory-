import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-!
# Narayana-cow-sequence cardinality cut-off

Seventh external sequence in the cut-off applications family.
Narayana's cow numbers `N_n` with `N_0 = N_1 = N_2 = 1` and the
recurrence `N_{n+3} = N_{n+2} + N_n` (one-shift cousin of Padovan
`P_{n+3} = P_{n+1} + P_n`).

`N_n` grows as `ρ^n` where `ρ ≈ 1.4656` is the supergolden ratio
(real root of `x³ = x² + 1`).  Faster growth than Padovan
(`1.3247`) but slower than Tribonacci (`1.839`).

## Catalogue coincidences

| n | N_n | catalogue role          |
|---|-----|-------------------------|
| 3 | 2   | NT (atomic generator)   |
| 4 | 3   | NS (atomic generator)   |
| 8 | 13  | catalogue prime         |

★ **Narayana misses the catalogue atoms `5` and `7` entirely**.
The sequence jumps `(N_6, N_7, N_8) = (6, 9, 13)`, skipping over
both `7` and any reading of `d = 5`.  Distinct fingerprint from
the other Direction C sequences: only Narayana exhibits a
"gapped" Hunter coverage at the small atoms.

The first two hits `(N_3, N_4) = (NT, NS)` mirror Fibonacci's
consecutive opening — but Narayana then peels off at the third
generator `d = 5` (Fibonacci nails `F_5 = 5`; Narayana lands on
`N_5 = 4`).

## Cut-off slices

  · **Depth 1 (M_1 = 3125)**: cut-off at `n ≥ 23`
    (`N_22 = 2745 < 3125 < 4023 = N_23`).
  · **Depth 2 restricted (M_{2,r} = 9 765 625)**: cut-off at
    `n ≥ 44` (`N_43 = 8 407 925 < M_{2,r} < 12 322 413 = N_44`).

## Cross-references

  · `cardinality_cutoff_applications.md` — applications family.
  · `PadovanCutoff.lean` — close relative (one-index-shift on the
    third-term recurrence).
-/

namespace E213.Lib.Math.Cohomology.Fractal.NarayanaCutoff

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff (M2r depth2Value
  asymptotic_cutoff_at_depth_2_restricted)

/-! ## §1 Narayana cow sequence -/

/-- Narayana cow sequence: `N_0 = N_1 = N_2 = 1`,
    `N_{n+3} = N_{n+2} + N_n`.  One-index shift of Padovan
    `P_{n+3} = P_{n+1} + P_n`. -/
def Nara : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => Nara (n + 2) + Nara n

/-! ## §2 Small-value table -/

theorem Nara_0  : Nara 0  = 1 := rfl
theorem Nara_1  : Nara 1  = 1 := rfl
theorem Nara_2  : Nara 2  = 1 := rfl
theorem Nara_3  : Nara 3  = 2 := by decide
theorem Nara_4  : Nara 4  = 3 := by decide
theorem Nara_5  : Nara 5  = 4 := by decide
theorem Nara_6  : Nara 6  = 6 := by decide
theorem Nara_7  : Nara 7  = 9 := by decide
theorem Nara_8  : Nara 8  = 13 := by decide
theorem Nara_9  : Nara 9  = 19 := by decide
theorem Nara_10 : Nara 10 = 28 := by decide
theorem Nara_22 : Nara 22 = 2745 := by decide
theorem Nara_23 : Nara 23 = 4023 := by decide
theorem Nara_43 : Nara 43 = 8407925 := by decide
theorem Nara_44 : Nara 44 = 12322413 := by decide

/-! ## §3 Catalogue coincidences

    Narayana hits the catalogue at indices `{3, 4, 8}`.  Three
    Hunter catalogue atoms, but the sequence MISSES the
    generators `5` and `7` entirely (jumps `4, 6, 9, 13` past
    both). -/

/-- `N_3 = 2 = NT` (atomic generator). -/
theorem Nara_3_eq_NT : Nara 3 = 2 := Nara_3

/-- `N_4 = 3 = NS` (atomic generator). -/
theorem Nara_4_eq_NS : Nara 4 = 3 := Nara_4

/-- `N_8 = 13` (catalogue prime). -/
theorem Nara_8_eq_13 : Nara 8 = 13 := Nara_8

/-- ★ **Narayana opens with `(NT, NS)` then peels off**:
    `(N_3, N_4) = (2, 3) = (NT, NS)` mirrors Fibonacci's opening,
    but at the third generator Narayana lands on `N_5 = 4` while
    Fibonacci nails `F_5 = 5`.  Direction C's first sequence with
    a "broken" Hunter triple at small indices. -/
theorem Nara_3_4_eq_NT_NS : Nara 3 = 2 ∧ Nara 4 = 3 := ⟨Nara_3, Nara_4⟩

/-- ★ **Gap over `{5, 7}`**: Narayana jumps over both catalogue
    atoms `5` and `7`.  `N_5 = 4 < 5 < 6 = N_6` and
    `N_6 = 6 < 7 < 9 = N_7`. -/
theorem Nara_skips_5 : Nara 5 < 5 ∧ 5 < Nara 6 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem Nara_skips_7 : Nara 6 < 7 ∧ 7 < Nara 7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §4 Depth-1 cut-off application

    `M_1 = 3125`.  Boundary `N_22 = 2745 < 3125 < 4023 = N_23`. -/

theorem Nara_22_below_M1 : Nara 22 < 3125 := by decide
theorem Nara_23_above_M1 : 3125 < Nara 23 := by decide

/-- Narayana threads the depth-1 boundary 898 above `M_1`. -/
theorem Nara_23_minus_M1_is_898 : Nara 23 - 3125 = 898 := by decide

/-- ★ **Depth-1 cut-off witness for Narayana**: `N_23 = 4023`
    exceeds `M_1 = 3125`. -/
theorem Nara_23_exceeds_depth_1 : 3125 < Nara 23 := Nara_23_above_M1

theorem Nara_23_not_at_depth_1 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ Nara 23
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ Nara 23
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ Nara 23
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ Nara 23 :=
  fun i j => asymptotic_cutoff_at_depth_1 (Nara 23) i j Nara_23_above_M1

/-! ## §5 Depth-2-restricted cut-off application

    `M_{2,r} = 9 765 625`.  Boundary `N_43 = 8 407 925 < M_{2,r}
    < 12 322 413 = N_44`. -/

theorem Nara_43_below_M2r : Nara 43 < M2r := by decide
theorem Nara_44_above_M2r : M2r < Nara 44 := by decide

/-- ★ **Depth-2-restricted cut-off witness for Narayana**:
    `N_44 = 12 322 413` exceeds `M_{2,r} = 9 765 625`. -/
theorem Nara_44_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ Nara 44 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted (Nara 44)
      Nara_44_above_M2r a b c d opL opR opOut

/-! ## §6 Capstone -/

/-- ★★★ **Capstone**: Narayana catalogue intersections (with the
    structurally distinguished `{5, 7}` gap) + cut-off boundaries. -/
theorem capstone :
    -- Opens with (NT, NS) at small indices
    (Nara 3 = 2 ∧ Nara 4 = 3)
    -- Misses generators 5 and 7
    ∧ (Nara 5 < 5 ∧ 5 < Nara 6)
    ∧ (Nara 6 < 7 ∧ 7 < Nara 7)
    -- Third catalogue hit (jump over the missing atoms)
    ∧ Nara 8 = 13
    -- Depth-1 cut-off boundary
    ∧ 3125 < Nara 23
    -- Depth-2-restricted cut-off boundary
    ∧ M2r < Nara 44 :=
  ⟨Nara_3_4_eq_NT_NS, Nara_skips_5, Nara_skips_7, Nara_8_eq_13,
   Nara_23_above_M1, Nara_44_above_M2r⟩

end E213.Lib.Math.Cohomology.Fractal.NarayanaCutoff
