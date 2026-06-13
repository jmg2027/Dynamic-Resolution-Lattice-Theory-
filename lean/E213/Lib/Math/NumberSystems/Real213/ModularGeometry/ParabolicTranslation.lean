import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicBoost

/-!
# The parabolic translation is a product of two reflections — completing the trichotomy

`FoldReflections` gave the **elliptic** face (`S = N · R`, a rotation, reflections in intersecting
mirrors) and `HyperbolicBoost` the **hyperbolic** face (`G = A · B`, a boost, ultraparallel mirrors).
The third face is **parabolic**: the translation

  `T = [[1, 1], [0, 1]]`   (`det = 1`, `trace = 2`, `disc = tr² − 4 = 0`)

a product of two reflections in **parallel** mirrors,

  `T = Aₚ · Bₚ`,   `Aₚ = [[1, 0], [0, −1]]`,  `Bₚ = [[1, 1], [0, −1]]`,

both involutions with `det = −1`.  So the entire `SL(2,ℤ)` order-2 trichotomy is one frame —
**product of two reflections** — with the single discriminant `tr² − 4` selecting the face:

  - `disc < 0` (`|tr| < 2`) — **elliptic**, intersecting mirrors → rotation (`S`, periodic);
  - `disc = 0` (`|tr| = 2`) — **parabolic**, parallel mirrors → translation (`T`, the difference-Lens
    depth-1 rung, `EllipticPeriodicTier.parabolic_iff_depth1`);
  - `disc > 0` (`|tr| > 2`) — **hyperbolic**, ultraparallel mirrors → boost (`G`, aperiodic).

The reflection decomposition is the common frame for all three; `tr² − 4` is the dial.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ParabolicTranslation

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul I2 S)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FoldReflections (N R)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicBoost (A B G)

/-- The parabolic translation `T = [[1,1],[0,1]]` (`det = 1`, `trace = 2`, `disc = 0`). -/
def T : Mat2 := ⟨1, 1, 0, 1⟩

/-- First parallel-mirror reflection `Aₚ = [[1,0],[0,−1]]`. -/
def Ap : Mat2 := ⟨1, 0, 0, -1⟩

/-- Second parallel-mirror reflection `Bₚ = [[1,1],[0,−1]]`. -/
def Bp : Mat2 := ⟨1, 1, 0, -1⟩

/-! ## `Aₚ`, `Bₚ` are reflections; their product is the translation -/

theorem Ap_involutive : mul Ap Ap = I2 := by decide
theorem Bp_involutive : mul Bp Bp = I2 := by decide
theorem Ap_det : Ap.a * Ap.d - Ap.b * Ap.c = -1 := by decide
theorem Bp_det : Bp.a * Bp.d - Bp.b * Bp.c = -1 := by decide

/-- ★★★ **`Aₚ · Bₚ = T`.**  Two reflections in parallel mirrors compose to the parabolic
    translation. -/
theorem parabolic_translation_eq : mul Ap Bp = T := by decide

/-- ★★ **`T` is parabolic.**  `det = 1`, `trace = 2`, `disc = tr² − 4 = 0` — the boundary between
    elliptic and hyperbolic, the repeated-eigenvalue / difference-Lens depth-1 rung. -/
theorem T_parabolic :
    T.a * T.d - T.b * T.c = 1 ∧ T.a + T.d = 2 ∧ (T.a + T.d) * (T.a + T.d) - 4 = 0 := by decide

/-- ★★★★ **The `SL(2,ℤ)` order-2 trichotomy as products of two reflections.**  Each face is a
    product of two `det = −1` reflections, and the discriminant `tr² − 4` selects which:
    elliptic `S = N · R` (`disc = −4 < 0`, rotation), parabolic `T = Aₚ · Bₚ` (`disc = 0`,
    translation), hyperbolic `G = A · B` (`disc = 5 > 0`, boost).  One frame, one dial, three
    faces. -/
theorem sl2_trichotomy_as_two_reflections :
    (mul N R = S ∧ (S.a + S.d) * (S.a + S.d) - 4 = -4)
    ∧ (mul Ap Bp = T ∧ (T.a + T.d) * (T.a + T.d) - 4 = 0)
    ∧ (mul A B = G ∧ (G.a + G.d) * (G.a + G.d) - 4 = 5) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ParabolicTranslation
