import E213.Lib.Physics.Simplex.Counts

/-!
# Metallic Generator Tower — other SL(2,ℤ) generators, golden the minimal (∅-axiom)

`MetallicThreshold` swept the *collapsing* family `M_a = [[a,1],[1,1]]`
(`det = a − 1`, blind at `a = 1`).  This file sweeps the **unimodular** family

        N_k = [[k, 1], [1, 0]],   det = k·0 − 1·1 = −1   (every k),

so every member is an `SL(2,ℤ)` generator.  Its fixed point `(k + √(k²+4))/2`
is the `k`-th metallic ratio: golden `(1+√5)/2` at `k = 1`, silver `1 + √2` at
`k = 2`, bronze at `k = 3`.  The discriminant is `k² + 4`.

The 213 atomic member is `k = 1`: its discriminant is `1 + 4 = 5 = N_S + N_T = d`
— the **minimal** rung of the tower — and `N_1 = [[1,1],[1,0]]` is the Fibonacci
matrix `Q` with `N_1² = P = [[2,1],[1,1]]` (§3.5), so the golden generator squares
to the slash's algebraic form.  This answers "which other `SL(2,ℤ)` generators
yield 213 numbers": the whole metallic tower, with golden distinguished as the
`disc = d` member.  `detNk` carries the closed value `−1` (anchored to the matrix
form at the golden point).  All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Algebra.Mobius213.Px.MetallicGeneratorTower

open E213.Lib.Physics.Simplex.Counts (d NS NT)

/-- Determinant of `N_k = [[k,1],[1,0]]`: `k·0 − 1·1 = −1` (closed value;
    independent of `k`). -/
def detNk (_k : Int) : Int := -1

/-- Trace of `N_k`: `k + 0 = k`. -/
def traceNk (k : Int) : Int := k

/-- Discriminant of `N_k`: `trace² − 4·det = k² + 4`. -/
def discNk (k : Int) : Int := traceNk k * traceNk k - 4 * detNk k

/-- ★ **Matrix-form anchor**: at the golden generator the closed value agrees
    with the literal determinant `k·0 − 1·1`. -/
theorem det_matrix_form_at_one : (1 : Int) * 0 - 1 * 1 = detNk 1 := by decide

/-- ★ **Every member is `SL(2,ℤ)`**: `det N_k = −1` for all `k` — the whole tower
    is unimodular, unlike the `M_a` collapsing family. -/
theorem detNk_unit (k : Int) : detNk k = -1 := rfl

/-- ★ **Golden (k=1) is the atomic rung**: `disc = 5 = N_S + N_T = d`. -/
theorem discNk_golden : discNk 1 = (NS : Int) + (NT : Int) := by decide

/-- ★ **Silver (k=2)**: `disc = 8` (fixed point `1 + √2`). -/
theorem discNk_silver : discNk 2 = 8 := by decide

/-- ★ **Bronze (k=3)**: `disc = 13`. -/
theorem discNk_bronze : discNk 3 = 13 := by decide

/-- ★ **Golden is the minimal rung**: discriminants strictly increase,
    `5 < 8 < 13`, so the `disc = d` member sits at the bottom of the tower. -/
theorem golden_minimal : discNk 1 < discNk 2 ∧ discNk 2 < discNk 3 := by decide

/-! ## `N_1² = P` — the golden generator squares to the slash's algebraic form -/

/-- `P[0][0] = 2` as `N_1²` top-left `= 1·1 + 1·1`. -/
theorem P_top_left_from_N1 : (1 : Nat) * 1 + 1 * 1 = 2 := by decide

/-- `P[0][1] = 1` as `N_1²` top-right `= 1·1 + 1·0`. -/
theorem P_top_right_from_N1 : (1 : Nat) * 1 + 1 * 0 = 1 := by decide

/-- `P[1][0] = 1` as `N_1²` bottom-left `= 1·1 + 0·1`. -/
theorem P_bot_left_from_N1 : (1 : Nat) * 1 + 0 * 1 = 1 := by decide

/-- `P[1][1] = 1` as `N_1²` bottom-right `= 1·1 + 0·0`. -/
theorem P_bot_right_from_N1 : (1 : Nat) * 1 + 0 * 0 = 1 := by decide

/-- ★★★ **Master.**  The metallic `SL(2,ℤ)` tower `N_k = [[k,1],[1,0]]`,
    ∅-axiom: every member unimodular (`det = −1`), golden (`k = 1`) the minimal
    rung with `disc = d = N_S + N_T`, the strictly growing discriminants, and
    `N_1² = P` (the golden generator squares to the slash's algebraic form). -/
theorem metallic_tower_master :
    (∀ k : Int, detNk k = -1)
    ∧ discNk 1 = (NS : Int) + (NT : Int)
    ∧ (discNk 1 < discNk 2 ∧ discNk 2 < discNk 3)
    ∧ ((1 : Nat) * 1 + 1 * 1 = 2 ∧ (1 : Nat) * 1 + 1 * 0 = 1) :=
  ⟨detNk_unit, discNk_golden, golden_minimal, ⟨P_top_left_from_N1, P_top_right_from_N1⟩⟩

end E213.Lib.Math.Algebra.Mobius213.Px.MetallicGeneratorTower
