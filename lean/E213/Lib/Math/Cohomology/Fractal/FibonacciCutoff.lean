import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff
import E213.Lib.Math.Cohomology.Fractal.LucasCutoff

/-!
# Fibonacci-sequence cardinality cut-off

Fourth external sequence in the cut-off applications family.
Fibonacci numbers `F_n` with `F_0 = 0`, `F_1 = 1`,
`F_{n+2} = F_{n+1} + F_n`.

`F_n` grows as `φ^n / √5` (golden ratio), so `F_n → ∞`.

## Catalogue coincidences

Fibonacci hits the Hunter atomic prime catalogue at **four**
indices, and remarkably **three of them are consecutive**:

| n | F_n | catalogue role                  |
|---|----|---------------------------------|
| 3 | 2  | `NT` (atomic generator)         |
| 4 | 3  | `NS` (atomic generator)         |
| 5 | 5  | `d` (atomic generator)          |
| 7 | 13 | catalogue prime (`= NS² + NT²`) |

★ **Three Hunter generators `{NT, NS, d}` appear at three
consecutive Fibonacci indices `{3, 4, 5}`** — the entire
canonical primitive set lives inside a length-3 window of the
Fibonacci sequence.

The `F_7 = 13` hit pairs with no other sequence we have considered;
Lucas jumps `L_5 = 11, L_6 = 18` over 13, Pell jumps `P_3 = 5,
P_4 = 12` then `P_5 = 29` over 13.

## Cut-off slices

  · **Depth 1 (M_1 = 3125)**: cut-off at `n ≥ 19`
    (`F_18 = 2584 < 3125 < 4181 = F_19`).
  · **Depth 2 restricted (M_{2,r} = 9 765 625)**: cut-off at
    `n ≥ 36` (`F_35 = 9 227 465 < M_{2,r} < 14 930 352 = F_36`).

## Cross-references

  · `cardinality_cutoff_applications.md` — applications family.
  · `PellCutoff.lean`, `LucasCutoff.lean` — sister sequence files.
-/

namespace E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff (M2r depth2Value
  asymptotic_cutoff_at_depth_2_restricted)
open E213.Lib.Math.Cohomology.Fractal.LucasCutoff (Lucas)

/-! ## §1 Fibonacci sequence -/

/-- Fibonacci sequence: `F_0 = 0`, `F_1 = 1`,
    `F_{n+2} = F_{n+1} + F_n`. -/
def Fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => Fib (n + 1) + Fib n

/-! ## §2 Small-value table -/

theorem Fib_0  : Fib 0  = 0 := rfl
theorem Fib_1  : Fib 1  = 1 := rfl
theorem Fib_2  : Fib 2  = 1 := by decide
theorem Fib_3  : Fib 3  = 2 := by decide
theorem Fib_4  : Fib 4  = 3 := by decide
theorem Fib_5  : Fib 5  = 5 := by decide
theorem Fib_6  : Fib 6  = 8 := by decide
theorem Fib_7  : Fib 7  = 13 := by decide
theorem Fib_8  : Fib 8  = 21 := by decide
theorem Fib_9  : Fib 9  = 34 := by decide
theorem Fib_10 : Fib 10 = 55 := by decide
theorem Fib_15 : Fib 15 = 610 := by decide
theorem Fib_18 : Fib 18 = 2584 := by decide
theorem Fib_19 : Fib 19 = 4181 := by decide
theorem Fib_20 : Fib 20 = 6765 := by decide
theorem Fib_35 : Fib 35 = 9227465 := by decide
theorem Fib_36 : Fib 36 = 14930352 := by decide

/-! ## §3 Four catalogue coincidences

    Fibonacci hits the catalogue at indices `{3, 4, 5, 7}`.
    Three consecutive hits at `{3, 4, 5}` embed the entire
    canonical Hunter primitive set `{NT, NS, d}`. -/

/-- `F_3 = 2 = NT` (atomic generator). -/
theorem Fib_3_eq_NT : Fib 3 = 2 := Fib_3

/-- `F_4 = 3 = NS` (atomic generator). -/
theorem Fib_4_eq_NS : Fib 4 = 3 := Fib_4

/-- `F_5 = 5 = d` (atomic generator). -/
theorem Fib_5_eq_d : Fib 5 = 5 := Fib_5

/-- ★ **Three consecutive Hunter generators**: `(F_3, F_4, F_5) =
    (NT, NS, d) = (2, 3, 5)`.  The canonical Hunter primitive set
    appears as three consecutive Fibonacci values. -/
theorem Fib_3_4_5_are_Hunter_generators :
    Fib 3 = 2 ∧ Fib 4 = 3 ∧ Fib 5 = 5 :=
  ⟨Fib_3, Fib_4, Fib_5⟩

/-- `F_7 = 13`, catalogue prime (= `NS² + NT² = 9 + 4`).  Fibonacci's
    fourth catalogue intersection. -/
theorem Fib_7_eq_13 : Fib 7 = 13 := Fib_7

/-! ## §4 Cross-sequence coincidences at generators

    Multiple sequences hit the small generators `{2, 3}`. -/

/-- `F_3 = Lucas L_0 = 2` (both equal `NT`). -/
theorem Fib_3_eq_Lucas_0 : Fib 3 = Lucas 0 := by decide

/-- `F_4 = Lucas L_2 = 3` (both equal `NS`). -/
theorem Fib_4_eq_Lucas_2 : Fib 4 = Lucas 2 := by decide

/-! ## §5 Depth-1 cut-off application

    `M_1 = 3125`.  Sharp boundary `F_18 = 2584 < 3125 < 4181 = F_19`. -/

theorem Fib_18_below_M1 : Fib 18 < 3125 := by decide
theorem Fib_19_above_M1 : 3125 < Fib 19 := by decide

/-- ★ **Depth-1 cut-off witness for Fibonacci**: `F_19 = 4181`
    exceeds `M_1 = 3125`. -/
theorem Fib_19_exceeds_depth_1 : 3125 < Fib 19 := Fib_19_above_M1

theorem Fib_19_not_at_depth_1 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ Fib 19
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ Fib 19
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ Fib 19
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ Fib 19 :=
  fun i j => asymptotic_cutoff_at_depth_1 (Fib 19) i j Fib_19_above_M1

/-! ## §6 Depth-2-restricted cut-off application

    `M_{2,r} = 9 765 625`.  Boundary `F_35 = 9 227 465 < M_{2,r}
    < 14 930 352 = F_36`. -/

theorem Fib_35_below_M2r : Fib 35 < M2r := by decide
theorem Fib_36_above_M2r : M2r < Fib 36 := by decide

/-- ★ **Depth-2-restricted cut-off witness for Fibonacci**: `F_36
    = 14_930_352` exceeds `M_{2,r} = 9 765 625`. -/
theorem Fib_36_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ Fib 36 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted (Fib 36)
      Fib_36_above_M2r a b c d opL opR opOut

/-! ## §7 Monotonicity (sample chain links) -/

theorem Fib_chain_5_6 : Fib 5 < Fib 6 := by decide
theorem Fib_chain_18_19 : Fib 18 < Fib 19 := by decide
theorem Fib_chain_35_36 : Fib 35 < Fib 36 := by decide

/-! ## §8 Capstone -/

/-- ★★★ **Capstone**: Fibonacci catalogue intersections + cut-off
    boundaries. -/
theorem capstone :
    -- Three consecutive Hunter generators
    (Fib 3 = 2 ∧ Fib 4 = 3 ∧ Fib 5 = 5)
    -- Fourth catalogue hit
    ∧ Fib 7 = 13
    -- Depth-1 cut-off boundary
    ∧ 3125 < Fib 19
    -- Depth-2-restricted cut-off boundary
    ∧ M2r < Fib 36 :=
  ⟨Fib_3_4_5_are_Hunter_generators, Fib_7_eq_13,
   Fib_19_above_M1, Fib_36_above_M2r⟩

end E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff
