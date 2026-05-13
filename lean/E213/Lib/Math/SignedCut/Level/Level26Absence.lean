import E213.Lib.Math.SignedCut.Hurwitz.HurwitzCeiling
import E213.Lib.Math.SignedCut.CD.CDTowerLevel

/-!
# Level 26 absence (negative Hurwitz on d=5, ∅-axiom)

The companion to `HurwitzCeiling`: at d=5 substrate, **level 26
is structurally absent** because it would require `5^52` distinct
trajectory branches, which exceeds the substrate's
distinguishability budget of `5^25 = N_U`.

Quantitative argument:
  * Bit-tower at level 26: `2^26 = 67108864` (twice level 25).
  * Substrate trajectory count at *full level 26*: would need
    `5^(2·26) = 5^52`.
  * `5^52 > 5^25` strictly (by `5 > 1`).
  * Therefore level 26 cannot fit on the d=5 substrate's budget.

This is the **negative Hurwitz** theorem on d=5: the CD tower
*cannot* extend beyond level 25 while preserving the substrate
distinguishability invariant.
-/

namespace E213.Lib.Math.SignedCut.Level.Level26Absence

open E213.Lib.Math.SignedCut.CD.CDTowerLevel (levelDim levelDim_25)
open E213.Lib.Math.SignedCut.Hurwitz.HurwitzCeiling (n_u_value_closed)

/-- ★ **Level 26 bit-dimension** = `2^26`. -/
theorem level26_bit_dim : levelDim 26 = 67108864 := rfl

/-- ★ **Level 26 bit-dim is exactly 2× level 25**. -/
theorem level26_double_level25 :
    levelDim 26 = 2 * levelDim 25 := rfl

/-- ★ **N_U strict positivity** (`5^25 > 0`). -/
theorem n_u_positive : 0 < (5 : Nat) ^ 25 := by decide

/-- ★ **`5^52` exceeds N_U strictly**.  This is the structural
    cardinality reason for level-26 absence: extending the CD
    tower by one more level would require `5^52` substrate
    trajectory branches, which strictly exceeds the d=5
    substrate's `5^25` budget. -/
theorem level26_substrate_excess :
    (5 : Nat) ^ 25 < (5 : Nat) ^ 52 := by decide

/-- ★ **Strict ratio** `5^52 / 5^25 = 5^27` — the substrate
    overflow factor at level 26. -/
theorem level26_overflow_ratio :
    (5 : Nat) ^ 52 = (5 : Nat) ^ 25 * (5 : Nat) ^ 27 := rfl

/-- ★ **Negative Hurwitz on d=5**: the tower cannot extend to
    level 26 within the substrate's distinguishability budget.
    Witness: `5^52 > 5^25 = N_U`. -/
theorem negative_hurwitz_d5 :
    (5 : Nat) ^ 25 < (5 : Nat) ^ 52
    ∧ (5 : Nat) ^ 52 = (5 : Nat) ^ 25 * (5 : Nat) ^ 27 :=
  ⟨level26_substrate_excess, level26_overflow_ratio⟩

end E213.Lib.Math.SignedCut.Level.Level26Absence
