import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-!
# Padovan-sequence cardinality cut-off

Sixth external sequence in the cut-off applications family.
Padovan numbers `P_n` with `P_0 = P_1 = P_2 = 1` and the recurrence
`P_{n+3} = P_{n+1} + P_n` (no `P_{n+2}` term — distinguishes from
Fibonacci / Tribonacci).

`P_n` grows as `ρ^n` where `ρ ≈ 1.3247` is the plastic constant
(real root of `x³ = x + 1`).  Slower-growth recurrence than
Tribonacci (`ψ ≈ 1.839`); reaches `M_1 = 3125` only at `n = 30`.

## Catalogue coincidences

| n | P_n | catalogue role          |
|---|-----|-------------------------|
| 3 | 2   | NT (atomic generator)   |
| 5 | 3   | NS (atomic generator)   |
| 7 | 5   | d (atomic generator)    |
| 8 | 7   | catalogue prime         |

★ **Three Hunter generators `{NT, NS, d}` appear at three
odd-index Padovan terms `{P_3, P_5, P_7}` in arithmetic
progression**.  Contrasts Fibonacci's `(F_3, F_4, F_5)`
consecutive-index window: Padovan threads the same primitive
set on the odd-index sub-lattice.

The fourth hit at `P_8 = 7` extends Fibonacci's three-catalogue
intersection by one.  Catalogue prime `13` is jumped over
(`P_12 = 21`, `P_13 = 28`).

## Cut-off slices

  · **Depth 1 (M_1 = 3125)**: cut-off at `n ≥ 30`
    (`P_29 = 2513 < 3125 < 3329 = P_30`).  Latest crossing in
    the applications family (Tribonacci at 16; Fibonacci at 19;
    Lucas / Pell at smaller indices).
  · **Depth 2 restricted (M_{2,r} = 9 765 625)**: cut-off at
    `n ≥ 59` (`P_58 = 8 745 217 < M_{2,r} < 11 584 946 = P_59`).

## Cross-references

  · `cardinality_cutoff_applications.md` — applications family.
  · `FibonacciCutoff.lean`, `TribonacciCutoff.lean` — sister
    sequence files (consecutive- and triple-recurrence variants).
-/

namespace E213.Lib.Math.Cohomology.Fractal.PadovanCutoff

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff (M2r depth2Value
  asymptotic_cutoff_at_depth_2_restricted)

/-! ## §1 Padovan sequence -/

/-- Padovan sequence: `P_0 = P_1 = P_2 = 1`,
    `P_{n+3} = P_{n+1} + P_n`. -/
def Pad : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => Pad (n + 1) + Pad n

/-! ## §2 Small-value table -/

theorem Pad_0  : Pad 0  = 1 := rfl
theorem Pad_1  : Pad 1  = 1 := rfl
theorem Pad_2  : Pad 2  = 1 := rfl
theorem Pad_3  : Pad 3  = 2 := by decide
theorem Pad_4  : Pad 4  = 2 := by decide
theorem Pad_5  : Pad 5  = 3 := by decide
theorem Pad_6  : Pad 6  = 4 := by decide
theorem Pad_7  : Pad 7  = 5 := by decide
theorem Pad_8  : Pad 8  = 7 := by decide
theorem Pad_9  : Pad 9  = 9 := by decide
theorem Pad_10 : Pad 10 = 12 := by decide
theorem Pad_29 : Pad 29 = 2513 := by decide
theorem Pad_30 : Pad 30 = 3329 := by decide
theorem Pad_58 : Pad 58 = 8745217 := by decide
theorem Pad_59 : Pad 59 = 11584946 := by decide

/-! ## §3 Catalogue coincidences

    Padovan hits the catalogue at indices `{3, 5, 7, 8}`.  Three
    of those — `{3, 5, 7}` — embed the canonical Hunter primitive
    set `{NT, NS, d}` at three odd indices in arithmetic
    progression (step 2). -/

/-- `P_3 = 2 = NT` (atomic generator). -/
theorem Pad_3_eq_NT : Pad 3 = 2 := Pad_3

/-- `P_5 = 3 = NS` (atomic generator). -/
theorem Pad_5_eq_NS : Pad 5 = 3 := Pad_5

/-- `P_7 = 5 = d` (atomic generator). -/
theorem Pad_7_eq_d : Pad 7 = 5 := Pad_7

/-- ★ **Triple Hunter-generator coincidence at odd indices**:
    `(P_3, P_5, P_7) = (NT, NS, d) = (2, 3, 5)`.  Sister to
    Fibonacci's consecutive-index `(F_3, F_4, F_5)` window;
    Padovan threads the same set on the odd-index sub-lattice
    in arithmetic progression of step 2. -/
theorem Pad_3_5_7_are_Hunter_generators :
    Pad 3 = 2 ∧ Pad 5 = 3 ∧ Pad 7 = 5 :=
  ⟨Pad_3, Pad_5, Pad_7⟩

/-- `P_8 = 7` (catalogue prime).  Fourth catalogue intersection. -/
theorem Pad_8_eq_7 : Pad 8 = 7 := Pad_8

/-! ## §4 Depth-1 cut-off application

    `M_1 = 3125`.  Boundary `P_29 = 2513 < 3125 < 3329 = P_30`. -/

theorem Pad_29_below_M1 : Pad 29 < 3125 := by decide
theorem Pad_30_above_M1 : 3125 < Pad 30 := by decide

/-- Padovan threads the depth-1 boundary 204 above `M_1`. -/
theorem Pad_30_minus_M1_is_204 : Pad 30 - 3125 = 204 := by decide

/-- ★ **Depth-1 cut-off witness for Padovan**: `P_30 = 3329`
    exceeds `M_1 = 3125`. -/
theorem Pad_30_exceeds_depth_1 : 3125 < Pad 30 := Pad_30_above_M1

theorem Pad_30_not_at_depth_1 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ Pad 30
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ Pad 30
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ Pad 30
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ Pad 30 :=
  fun i j => asymptotic_cutoff_at_depth_1 (Pad 30) i j Pad_30_above_M1

/-! ## §5 Depth-2-restricted cut-off application

    `M_{2,r} = 9 765 625`.  Boundary `P_58 = 8 745 217 < M_{2,r}
    < 11 584 946 = P_59`. -/

theorem Pad_58_below_M2r : Pad 58 < M2r := by decide
theorem Pad_59_above_M2r : M2r < Pad 59 := by decide

/-- ★ **Depth-2-restricted cut-off witness for Padovan**: `P_59
    = 11 584 946` exceeds `M_{2,r} = 9 765 625`. -/
theorem Pad_59_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ Pad 59 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted (Pad 59)
      Pad_59_above_M2r a b c d opL opR opOut

/-! ## §6 Capstone -/

/-- ★★★ **Capstone**: Padovan catalogue intersections + cut-off
    boundaries.  The odd-index `(P_3, P_5, P_7) = (NT, NS, d)`
    coincidence is the structural fingerprint distinguishing
    Padovan from the consecutive-index Fibonacci window. -/
theorem capstone :
    -- Three Hunter generators at odd indices
    (Pad 3 = 2 ∧ Pad 5 = 3 ∧ Pad 7 = 5)
    -- Fourth catalogue hit
    ∧ Pad 8 = 7
    -- Depth-1 cut-off boundary
    ∧ 3125 < Pad 30
    -- Depth-2-restricted cut-off boundary
    ∧ M2r < Pad 59 :=
  ⟨Pad_3_5_7_are_Hunter_generators, Pad_8_eq_7,
   Pad_30_above_M1, Pad_59_above_M2r⟩

end E213.Lib.Math.Cohomology.Fractal.PadovanCutoff
