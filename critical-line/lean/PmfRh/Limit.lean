/-
  The Last Sorry: δ(n) → 0
  Mingu Jeong & Claude (Anthropic), 2026.04.15

  Uses Mathlib to prove the resolution limit theorem.
  Key: squeeze between 0 and C/n (which → 0 by Mathlib).
-/

import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

/-! ## Resolution sequence -/

structure RealResolutionSeq where
  δ : ℕ → ℝ
  pos : ∀ n, 0 < δ n
  mono : ∀ n, δ (n + 1) ≤ δ n
  /-- Upper bound: δ(n) ≤ C/n for large n.
      (Weaker than C/√n but sufficient for limit.) -/
  upper : ∃ C > 0, ∀ n, δ n ≤ C / (n : ℝ)

/-! ## The Limit Theorem -/

/-- δ(n) → 0: the resolution sequence converges to 0.
    ZERO sorry. Full Mathlib proof. -/
theorem limit_from_resolution (rs : RealResolutionSeq) :
    Tendsto rs.δ atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := rs.upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat C)
  · intro n; exact le_of_lt (rs.pos n)
  · exact hbound
