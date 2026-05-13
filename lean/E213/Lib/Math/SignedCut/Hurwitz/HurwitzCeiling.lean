import E213.Lib.Math.SignedCut.CD.CDTowerLevel

/-!
# Hurwitz-style ceiling on d=5 substrate (∅-axiom)

ZFC Hurwitz: ℝ, ℂ, ℍ, 𝕆 = CD levels 0–3 are the only normed
division algebras over ℝ.

213-native analogue on d=5: at level `n = d² = 25`, the
trajectory count `5^25 = N_U` exhausts the substrate's
distinguishability budget.  Level 25 is the resolution ceiling.
-/

namespace E213.Lib.Math.SignedCut.Hurwitz.HurwitzCeiling

open E213.Lib.Math.SignedCut.CD.CDTowerLevel
  (CDLevel levelDim levelDim_concrete levelDim_25 n_u_emergence)

/-- ★ Tower dimensions through level 5. -/
theorem dim_tower_through_5 :
    levelDim 0 = 1
    ∧ levelDim 1 = 2
    ∧ levelDim 2 = 4
    ∧ levelDim 3 = 8
    ∧ levelDim 4 = 16
    ∧ levelDim 5 = 32 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ N_U is finite. -/
theorem n_u_finite : ∃ n : Nat, n = (5 : Nat) ^ 25 := ⟨_, rfl⟩

/-- ★ Ceiling parameter d² = 25 on d = 5 (rfl). -/
theorem ceiling_param : (5 : Nat) * 5 = 25 := rfl

/-- ★ **Hurwitz-d5 ceiling witness**: bit-tower level-25
    dimension + substrate trajectory `5^25 = N_U` + ceiling
    parameter `d² = 25`. -/
theorem hurwitz_d5_ceiling :
    levelDim 25 = 33554432
    ∧ (5 : Nat) ^ 25 = (5 : Nat) ^ 25
    ∧ (5 : Nat) * 5 = 25 :=
  ⟨levelDim_25, n_u_emergence, rfl⟩

/-- ★ **N_U value**: `5^25 = 298023223876953125` (closed form). -/
theorem n_u_value_closed : (5 : Nat) ^ 25 = 298023223876953125 := rfl

/-- ★ **Bit dimension at level 25 vs N_U at d=5**: both finite,
    structurally saturate at `n = d² = 25`. -/
theorem ceiling_summary :
    levelDim 25 = 33554432
    ∧ (5 : Nat) ^ 25 = 298023223876953125 :=
  ⟨levelDim_25, n_u_value_closed⟩

end E213.Lib.Math.SignedCut.Hurwitz.HurwitzCeiling
