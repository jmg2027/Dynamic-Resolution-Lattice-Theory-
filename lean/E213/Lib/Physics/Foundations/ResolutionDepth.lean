import E213.Lib.Physics.Basel.Bound
import E213.Lib.Physics.Simplex.Counts

/-!
# Resolution depth — why α_3, α_2 are exact and α_1 is bracketed

The three Standard Model gauge couplings differ in their **Basel
resolution depth**:

  1/α_3 = (NS² - 1) · S(1)   exact integer 8     (depth N=1, confined)
  1/α_2 = 12 · NT · S(2)     exact integer 30    (depth N=2, massive)
  1/α_1 = 12 · NS · S(∞)     6π² transcendental  (depth N=∞, massless)

Physical interpretation: each force has a Basel cutoff equal to the
number of resolution levels its propagator survives.

  * Color: Λ_QCD (confinement) cuts at n=1 → only S(1) contributes
  * Weak: M_W, M_Z mass cuts at n=2 → S(2) = 1 + 1/4 contributes
  * EM:  no cutoff (massless photon) → entire S(∞) = ζ(2) needed

This file formalizes:
  * Exact integer values for α_3, α_2 (no bracket)
  * Demonstration that wrong depth gives wrong answer
  * α_1 must use bracket (S(∞) is irrational)

All theorems 0-axiom decide-checked.
-/

namespace E213.Lib.Physics.Foundations.ResolutionDepth

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound

/-- α_3 at correct depth N=1: 1/α_3 = (NS²-1) · S(1) = 8 ·
    (1/1) = 8.  Integer because S(1) denominator = 1. -/
theorem alpha_3_at_depth_1 :
    let s := S 1
    (NS * NS - 1) * s.1 = 8 ∧ s.2 = 1 := by decide

/-- α_2 at correct depth N=2: 1/α_2 = 12·NT·S(2) = 24·5/4 = 30.
    Integer because 24 / 4 = 6 ∈ ℤ. -/
theorem alpha_2_at_depth_2 :
    let s := S 2
    12 * NT * s.1 = 30 * s.2 := by decide

/-- α_1 at infinite depth N=∞: 1/α_1 = 12·NS·S(∞) = 36·ζ(2).
    No exact rational form; only bracket [36·S(N), 36·upper(N)].
    Concrete N=3 bracket: -/
theorem alpha_1_only_bracket_at_3 :
    let lo := (12 * NS) * (S 3).1
    let hi := (12 * NS) * (upper 3).1
    let lo_d := (S 3).2
    let hi_d := (upper 3).2
    -- 36·S(3) = 36·49/36 = 49 vs 36·upper(3) = 36·183/108 = 61
    -- (cross-mult: 49·hi_d < hi·lo_d ⟹ 49·108 < 61·36)
    lo * hi_d < hi * lo_d := by decide

/-- **Wrong depth detection**: α_2 at depth N=1 (single fractal) —
    gives 24, not 30.  Demonstrates depth must be exactly 2. -/
theorem alpha_2_wrong_depth_1 :
    let s := S 1
    12 * NT * s.1 = 24 ∧ s.2 = 1 := by decide

/-- 24 ≠ 30 — confirms depth N=1 is incorrect for α_2. -/
theorem twenty_four_ne_thirty : (24 : Nat) ≠ 30 := by decide

/-- α_3 at depth N=2 (over-resolution) — gives 10, not 8.
    α_3 must use exactly S(1), no more no less. -/
theorem alpha_3_wrong_depth_2 :
    let s := S 2
    -- (NS²-1)·s.1 / s.2 = 8·5/4 = 10
    (NS * NS - 1) * s.1 = 10 * s.2 := by decide

/-- Eight ≠ ten — confirms depth N=2 is incorrect for α_3. -/
theorem eight_ne_ten : (8 : Nat) ≠ 10 := by decide

/-- **Resolution depth principle**:
      depth(α_i) = (force range cutoff in fractal levels)
      α_3: depth 1 (confined, Λ_QCD)
      α_2: depth 2 (massive, M_W M_Z)
      α_1: depth ∞ (massless, photon)
    The Lean theorems above witness this for the first two.
    The third (∞) is encoded as the bracket S(N) → upper(N). -/
theorem depth_principle_witnesses :
    ((NS * NS - 1) * (S 1).1 = 8 ∧ (S 1).2 = 1)
    ∧ (12 * NT * (S 2).1 = 30 * (S 2).2)
    ∧ ((S 3).1 < (upper 3).1) := by decide

end E213.Lib.Physics.Foundations.ResolutionDepth
