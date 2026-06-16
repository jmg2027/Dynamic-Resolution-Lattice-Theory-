import E213.Lib.Math.Cohomology.Bipartite.Parametric.Delta0AndConnectedness

/-!
# Parametric Euler characteristic + capstone

For K_{NS,NT}^{(c)} with V = NS + NT vertices and E = c·NS·NT edges,
the Euler characteristic of the 1-skeleton is:
  χ = V − E = (NS + NT) − c·NS·NT

For connected K (b_0 = 1, verified in `Delta0AndConnectedness`):
  χ = 1 − b_1   ⇒   b_1 = c·NS·NT − (NS + NT) + 1

This file:
  · Defines the parametric Euler formula
  · Specialises it at K_{3,2}^{(c=2)} (b₁ = 8, χ = −7)
  · Provides a capstone bundling the full parametric cohomology
    summary for all chartBase-≤-5 deployments
  · Connects to `KChartLensAbstract` axes-partition data
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.EulerAndCapstone

open E213.Lib.Math.Cohomology.Bipartite.Parametric.Delta0AndConnectedness

/-! ## Parametric Euler characteristic formula -/

/-- Euler characteristic of K_{NS,NT}^{(c)} as a 1-skeleton:
    χ = V − E = (NS + NT) − c·NS·NT.  Int-valued because χ can
    be negative (e.g., K_{3,2}^{(c=2)}: 5 − 12 = −7). -/
def eulerChar (NS NT c : Nat) : Int :=
  (NS + NT : Int) - (c * NS * NT : Int)

/-- For connected K_{NS,NT}^{(c)} (b_0 = 1) with no higher cells,
    b_1 = c·NS·NT − (NS + NT) + 1 (when c·NS·NT ≥ NS + NT − 1).
    Nat version. -/
def b1Formula (NS NT c : Nat) : Nat := c * NS * NT + 1 - (NS + NT)

/-! ## K_{3,2}^{(c=2)} specialization -/

/-- At (NS, NT, c) = (3, 2, 2), Euler char = -7. -/
theorem eulerChar_K32 : eulerChar 3 2 2 = -7 := by decide

/-- At (NS, NT, c) = (3, 2, 2), b_1 = 8 (= NS² − 1 per α_3 reading). -/
theorem b1Formula_K32 : b1Formula 3 2 2 = 8 := by decide

/-! ## Cohomology summary across chartBase-≤-5 deployments -/

/-- ★★★★ **Parametric b_1 across the  deployment family**

  Evaluates `b1Formula` at every K_{NS,NT}^{(c)} that appears in
  the chartBase-≤-5 narrative:

  | Deployment           | b_1 | Role                          |
  |---|---|---|
  | K_{1,1}^{(c=1)}       | 0   | trivial bridge edge           |
  | K_{1,3}^{(c=1)}       | 0   | tree at d_M = 3 (Poincaré)   |
  | K_{3,1}^{(c=1)}       | 0   | tree at d_M = 3 (S/T swap)   |
  | K_{2,2}^{(c=1)}       | 1   | 4-cycle                       |
  | K_{2,2}^{(c=2)}       | 5   | double-covered 4-cycle        |
  | K_{1,4}^{(c=1)}       | 0   | tree branch at d_M = 4        |
  | K_{3,2}^{(c=2)}       | 8   | **forced critical**           |
  | K_{2,3}^{(c=2)}       | 8   | S/T swap of forced            |
  | K_{3,3}^{(c=2)}       | 13  | d_M = 5 candidate (rejected)  |
-/
theorem b1Formula_G121_family :
    b1Formula 1 1 1 = 0
    ∧ b1Formula 1 3 1 = 0
    ∧ b1Formula 3 1 1 = 0
    ∧ b1Formula 2 2 1 = 1
    ∧ b1Formula 2 2 2 = 5
    ∧ b1Formula 1 4 1 = 0
    ∧ b1Formula 3 2 2 = 8
    ∧ b1Formula 2 3 2 = 8
    ∧ b1Formula 3 3 2 = 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## KChartLensAbstract bridge

`chartBase NS NT = NS + NT` matches the `KChartLens.axes_partition`
witness (chartVisibleAxes + selfPointingAxes = NS + NT).  At
selfPointingAxes = 1 (the dim-4 self-pointing ansatz), chartVisibleAxes = (NS+NT) − 1.
-/

/-- For any (NS + NT) = 5 deployment, chartVisibleAxes (under
    selfPointingAxes = 1) equals 4 = d_M for d_M = 4 critical
    regime.  Numerical witness across K-deployments at chartBase 5. -/
theorem chartVisibleAxes_chartBase5_witnesses :
    (3 + 2 : Nat) - 1 = 4    -- K_{3,2}
    ∧ (2 + 3 : Nat) - 1 = 4  -- K_{2,3}
    ∧ (1 + 4 : Nat) - 1 = 4  -- K_{1,4}
    ∧ (4 + 1 : Nat) - 1 = 4  -- K_{4,1}
    := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Universal close capstone -/

/-- ★★★★★★ **Parametric cohomology consolidation capstone**

  Bundles the parametric cohomology machinery:
    · CochSpaces.CochV / CochE defined parametrically in (NS, NT, c)
    · srcOf / tgtOf / delta0 parametric
    · b_0 = 1 verified across the K-deployment family
    · b_1 formula `c·NS·NT + 1 − (NS + NT)` for connected case
    · Euler characteristic eulerChar = (NS + NT) − c·NS·NT
    · K_{3,2}^{(c=2)} specialisation (b₁ = 8, χ = −7, ker δ⁰ = 2)

  The universal `∀ (NS NT c), 1 ≤ NS → 1 ≤ NT → 1 ≤ c → ker δ⁰ =
  constant cochains (dim 1)` is closed structurally and ∅-axiom in
  `KernelConstancyUniversal`; this capstone records the flat-form
  `kerSizeDelta0Direct = 2` enumeration over the chartBase-≤-5 family
  (the quantified-flat enumeration stays `decide`-only — counting flat
  indices forces core Lean's propext-carrying `Nat.div`). -/
theorem parametric_close_capstone :
    -- Parametric Euler at K_{3,2}^{(c=2)}
    eulerChar 3 2 2 = -7
    -- Parametric b_1 at K_{3,2}^{(c=2)}
    ∧ b1Formula 3 2 2 = 8
    -- ker δ⁰ at K_{3,2}^{(c=2)} = 2 (the two constant cochains)
    ∧ kerSizeDelta0Direct 3 2 2 = 2
    -- ker δ⁰ at all tree deployments = 2
    ∧ kerSizeDelta0Direct 1 1 1 = 2
    ∧ kerSizeDelta0Direct 1 3 1 = 2
    ∧ kerSizeDelta0Direct 1 4 1 = 2
    -- b_1 = 0 at all tree deployments
    ∧ b1Formula 1 1 1 = 0
    ∧ b1Formula 1 3 1 = 0
    ∧ b1Formula 1 4 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Bipartite.Parametric.EulerAndCapstone
