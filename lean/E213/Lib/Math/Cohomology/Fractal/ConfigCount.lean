import E213.Lib.Math.Cohomology.Fractal.Level

/-!
# Fractal-level configuration count

G120 Phase 1 — establish the parametric Lens-output family.

`configCount n` is the count-Lens readout at fractal level `n` —
number of distinguishable configurations of a fractal complex with
`numV n = 5^n` vertices, each carrying `d = 5` states.

This is the **parametric family**.  The earlier privileged name
`N_U` (per G120) is just `configCount 2` — one value of this
family, not a privileged constant.

Per CLAUDE.md "Universe-constant framing" failure mode + G120
Round 3: numerical readouts are Lens outputs, parametric over the
level.

## Values

| n | numV n = 5^n | configCount n = 5^(5^n) |
|---|---|---|
| 0 | 1 | 5 |
| 1 | 5 | 3125 |
| 2 | 25 | 298023223876953125 (= "N_U" historically) |
| 3 | 125 | 5^125 (≈ 2.35 × 10^87) |
-/

namespace E213.Lib.Math.Cohomology.Fractal.ConfigCount

open E213.Lib.Math.Cohomology.Fractal.Level (numV)

/-- Configuration count at fractal level `n`: `5^(numV n) = 5^(5^n)`.

    This is the parametric Lens-output family.  Per G120 Round 3
    sharpening: the previously-privileged `N_U = 5^25` is
    `configCount 2` — one value of this family. -/
def configCount (n : Nat) : Nat := 5 ^ (numV n)

/-! ## Concrete values (decide-checked) -/

/-- `configCount 0 = 5^1 = 5`. -/
theorem configCount_zero : configCount 0 = 5 := by decide

/-- `configCount 1 = 5^5 = 3125`. -/
theorem configCount_one : configCount 1 = 3125 := by decide

/-- `configCount 2 = 5^25 = 298_023_223_876_953_125`.

    This is the value historically called `N_U`.  Demoted to one
    value of the `configCount` family per G120. -/
theorem configCount_two : configCount 2 = 298023223876953125 := by decide

/-- `configCount 2 = 5^25` (structural form). -/
theorem configCount_two_pow : configCount 2 = 5 ^ 25 := by decide

/-! ## Bridge to `numV` -/

/-- `configCount n = 5 ^ numV n`.  Unfolds the definition. -/
theorem configCount_eq_pow_numV (n : Nat) :
    configCount n = 5 ^ numV n := rfl

end E213.Lib.Math.Cohomology.Fractal.ConfigCount
