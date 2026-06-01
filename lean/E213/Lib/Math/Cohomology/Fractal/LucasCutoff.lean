import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff
import E213.Lib.Math.Cohomology.Fractal.PellCutoff

/-!
# Lucas-sequence cardinality cut-off

Applies the cardinality cut-off principle to a third external
sequence: Lucas numbers `L_n` with `L_0 = 2`, `L_1 = 1`,
`L_{n+2} = L_{n+1} + L_n`.

`L_n` grows as `φ^n` (golden ratio), so `L_n → ∞`.

## Catalogue coincidences

Lucas intersects the Hunter atomic prime catalogue at **five**
indices, more than any other external sequence considered:

| n  | L_n | catalogue role                         |
|----|-----|----------------------------------------|
| 0  | 2   | `NT` (atomic generator)                |
| 2  | 3   | `NS` (atomic generator)                |
| 4  | 7   | catalogue prime (= `NS² − NT`)         |
| 7  | 29  | catalogue (= `d² + NT² = NT^d − NS`)   |
| 13 | 521 | catalogue prime, `Φ_10(5)`             |

The `L_7 = 29` coincidence aligns with `Pell P_5 = 29 = Aurifeuillean L_1`
(three external sequences agreeing on the smallest depth-2 catalogue
atom).  The `L_13 = 521` coincidence aligns with the Aurifeuillean
cyclotomic value `Φ_10(5) = 521` (catalogue handle of
`configCount 2 + 1`).

## Cut-off slices

  · **Depth 1 (M_1 = 3125)**: cut-off at `n ≥ 17`
    (`L_16 = 2207 < 3125 < 3571 = L_17`).
  · **Depth 2 restricted (M_{2,r} = 9 765 625)**: cut-off at `n ≥ 34`
    (`L_33 = 7 881 196 < M_{2,r} < 12 752 043 = L_34`).

## Cross-references

  · `cardinality_cutoff_applications.md` — applications family.
  · `PellCutoff.lean` — Pell sequence cut-off.
  · `AurifeuilleanFullCutoff.lean` — depth-1 substrate.
  · `AurifeuilleanDepth2Cutoff.lean` — restricted depth-2.
-/

namespace E213.Lib.Math.Cohomology.Fractal.LucasCutoff

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff (M2r depth2Value
  asymptotic_cutoff_at_depth_2_restricted)
open E213.Lib.Math.Cohomology.Fractal.PellCutoff (Pell)

/-! ## §1 Lucas sequence -/

/-- Lucas sequence: `L_0 = 2`, `L_1 = 1`,
    `L_{n+2} = L_{n+1} + L_n`. -/
def Lucas : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => Lucas (n + 1) + Lucas n

/-! ## §2 Small-value table -/

theorem Lucas_0  : Lucas 0  = 2 := rfl
theorem Lucas_1  : Lucas 1  = 1 := rfl
theorem Lucas_2  : Lucas 2  = 3 := by decide
theorem Lucas_3  : Lucas 3  = 4 := by decide
theorem Lucas_4  : Lucas 4  = 7 := by decide
theorem Lucas_5  : Lucas 5  = 11 := by decide
theorem Lucas_6  : Lucas 6  = 18 := by decide
theorem Lucas_7  : Lucas 7  = 29 := by decide
theorem Lucas_8  : Lucas 8  = 47 := by decide
theorem Lucas_9  : Lucas 9  = 76 := by decide
theorem Lucas_10 : Lucas 10 = 123 := by decide
theorem Lucas_11 : Lucas 11 = 199 := by decide
theorem Lucas_12 : Lucas 12 = 322 := by decide
theorem Lucas_13 : Lucas 13 = 521 := by decide
theorem Lucas_14 : Lucas 14 = 843 := by decide
theorem Lucas_15 : Lucas 15 = 1364 := by decide
theorem Lucas_16 : Lucas 16 = 2207 := by decide
theorem Lucas_17 : Lucas 17 = 3571 := by decide
theorem Lucas_18 : Lucas 18 = 5778 := by decide
theorem Lucas_19 : Lucas 19 = 9349 := by decide
theorem Lucas_20 : Lucas 20 = 15127 := by decide
theorem Lucas_33 : Lucas 33 = 7881196 := by decide
theorem Lucas_34 : Lucas 34 = 12752043 := by decide

/-! ## §3 Five catalogue coincidences

    Lucas hits the catalogue at indices `{0, 2, 4, 7, 13}`. -/

/-- `L_0 = 2 = NT` (atomic generator). -/
theorem Lucas_0_eq_NT : Lucas 0 = 2 := Lucas_0

/-- `L_2 = 3 = NS` (atomic generator). -/
theorem Lucas_2_eq_NS : Lucas 2 = 3 := Lucas_2

/-- `L_4 = 7`, catalogue prime `(= NS² − NT)`. -/
theorem Lucas_4_eq_7 : Lucas 4 = 7 := Lucas_4

/-- ★ `L_7 = 29` — coincides with Pell `P_5 = 29` AND with
    Aurifeuillean `L_1 = 29`.  Triple-sequence agreement at the
    smallest depth-2 catalogue atom. -/
theorem Lucas_7_eq_Pell_5 : Lucas 7 = Pell 5 := by decide

/-- ★ `L_13 = 521` — catalogue prime, equals the Aurifeuillean
    cyclotomic value `Φ_10(5)`.  Lucas hits the Aurifeuillean
    handle of `configCount 2 + 1`. -/
theorem Lucas_13_eq_521 : Lucas 13 = 521 := Lucas_13

/-! ## §4 Depth-1 cut-off application

    Hunter depth-1 uniform bound `M_1 = 3125`.  Boundary:
    `L_16 = 2207 < 3125 < 3571 = L_17`.  Cut-off starts at `n = 17`. -/

theorem Lucas_16_below_M1 : Lucas 16 < 3125 := by decide
theorem Lucas_17_above_M1 : 3125 < Lucas 17 := by decide

/-- ★ **Depth-1 cut-off witness for Lucas**: `L_17 = 3571`
    exceeds the Hunter depth-1 uniform bound `M_1 = 3125`. -/
theorem Lucas_17_exceeds_depth_1 : 3125 < Lucas 17 := Lucas_17_above_M1

/-- Apply `asymptotic_cutoff_at_depth_1` to Lucas. -/
theorem Lucas_17_not_at_depth_1 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ Lucas 17
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ Lucas 17
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ Lucas 17
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ Lucas 17 :=
  fun i j => asymptotic_cutoff_at_depth_1 (Lucas 17) i j Lucas_17_above_M1

/-! ## §5 Depth-2 restricted cut-off application

    Restricted depth-2 bound `M_{2,r} = 9 765 625`.  Boundary:
    `L_33 = 7 881 196 < M_{2,r} < 12 752 043 = L_34`.  Cut-off
    starts at `n = 34`. -/

theorem Lucas_33_below_M2r : Lucas 33 < M2r := by decide
theorem Lucas_34_above_M2r : M2r < Lucas 34 := by decide

/-- ★ **Depth-2-restricted cut-off witness for Lucas**: `L_34
    = 12_752_043` exceeds the restricted depth-2 uniform bound
    `M_{2,r} = 9 765 625`. -/
theorem Lucas_34_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ Lucas 34 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted (Lucas 34)
      Lucas_34_above_M2r a b c d opL opR opOut

/-! ## §6 Monotonicity (sample chain links) -/

theorem Lucas_chain_2_3 : Lucas 2 < Lucas 3 := by decide
theorem Lucas_chain_16_17 : Lucas 16 < Lucas 17 := by decide
theorem Lucas_chain_33_34 : Lucas 33 < Lucas 34 := by decide

/-! ## §7 Capstone

    Lucas, Pell, and Aurifeuillean all admit the cut-off principle.
    The three external sequences share two structural coincidences:

      · `L_7 = P_5 = AurifeuilleanL_1 = 29` (triple agreement at
        the catalogue atom `29 = d² + NT² = NT^d − NS`).
      · `L_13 = Φ_10(5) = 521` (Lucas-Aurifeuillean agreement on
        the catalogue prime `521`, the Aurifeuillean handle of
        `configCount 2 + 1`).

    These coincidences are the principle's "locate" step
    instantiated across multiple sequences; the agreement points
    are catalogue atoms with multiple Hunter readings. -/

/-- ★★★ **Capstone**: Lucas cut-off + triple-sequence coincidence. -/
theorem capstone :
    -- Lucas catalogue intersections
    Lucas 0 = 2
    ∧ Lucas 2 = 3
    ∧ Lucas 4 = 7
    ∧ Lucas 7 = 29
    ∧ Lucas 13 = 521
    -- Triple agreement at 29
    ∧ Lucas 7 = Pell 5
    -- Depth-1 cut-off boundary
    ∧ 3125 < Lucas 17
    -- Depth-2-restricted cut-off boundary
    ∧ M2r < Lucas 34 :=
  ⟨Lucas_0, Lucas_2, Lucas_4, Lucas_7, Lucas_13,
   Lucas_7_eq_Pell_5, Lucas_17_above_M1, Lucas_34_above_M2r⟩

end E213.Lib.Math.Cohomology.Fractal.LucasCutoff
