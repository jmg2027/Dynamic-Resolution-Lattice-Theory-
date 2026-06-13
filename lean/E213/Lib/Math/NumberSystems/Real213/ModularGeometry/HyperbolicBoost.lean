import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FoldReflections

/-!
# The golden iterator is a product of two reflections — the hyperbolic boost

`FoldReflections` showed the *elliptic* generator `S = N · R` is a product of two reflections in
intersecting mirrors — a **rotation** (`det = +1`, `|trace| = 0 < 2`, finite order).  The same
"product of two reflections" gives, in ultraparallel mirrors, a **boost** — the hyperbolic case.  The
golden iterator

  `G = [[2, 1], [1, 1]]`   (φ's Möbius iterator `z ↦ (2z+1)/(z+1)`, `det = 1`)

is hyperbolic: `trace = 3 > 2`, discriminant `tr² − 4 = 5 = NS + NT` (the golden discriminant,
`phi_pi_poles`), so its eigenvalues are real (`φ²`, `φ⁻²`) and it has **infinite order** — no periodic
floor.  It factors as a product of two reflections

  `G = A · B`,   `A = [[1, 0], [−1, −1]]`,  `B = [[2, 1], [−3, −2]]`

with `A² = B² = I`, `det A = det B = −1`.  So every `SL(2,ℤ)` element (`det = +1`) is a product of two
reflections (`det = −1`), and whether the product is a **rotation** (elliptic, `|tr| < 2`, periodic)
or a **boost** (hyperbolic, `|tr| > 2`, aperiodic) is read off the single number `|trace|` against
the central value `2` — the same `tr² − 4` discriminant that runs the order-2 dial
(`EllipticPeriodicTier`).  The reflection decomposition is the common frame; the trace decides the
face.  φ lives on the boost; π lives on the rotation taken to an irrational angle.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicBoost

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul I2)

/-- The golden iterator `G = [[2,1],[1,1]]` — φ's Möbius map, `det = 1`, hyperbolic. -/
def G : Mat2 := ⟨2, 1, 1, 1⟩

/-- First reflection `A = [[1,0],[−1,−1]]` (`det = −1`, involution). -/
def A : Mat2 := ⟨1, 0, -1, -1⟩

/-- Second reflection `B = [[2,1],[−3,−2]]` (`det = −1`, involution). -/
def B : Mat2 := ⟨2, 1, -3, -2⟩

/-! ## `A`, `B` are reflections -/

theorem A_involutive : mul A A = I2 := by decide
theorem B_involutive : mul B B = I2 := by decide
theorem A_det : A.a * A.d - A.b * A.c = -1 := by decide
theorem B_det : B.a * B.d - B.b * B.c = -1 := by decide

/-! ## Their product is the golden boost -/

/-- ★★★ **`A · B = G`.**  Two reflections compose to the golden hyperbolic iterator (a boost). -/
theorem golden_boost_eq : mul A B = G := by decide

/-- `G` is orientation-preserving (`det = +1`) — the product of the two `det = −1` reflections. -/
theorem G_det : G.a * G.d - G.b * G.c = 1 := by decide

/-- ★★ **`G` is hyperbolic.**  `trace = 3` (so `|trace| > 2`) and discriminant `tr² − 4 = 5`
    (`= NS + NT`, the golden discriminant `> 0`) — real eigenvalues, infinite order, no periodic
    floor.  Contrast the elliptic generators `S` (`|tr| = 0`), `U` (`|tr| = 1`), both `< 2`. -/
theorem G_hyperbolic : G.a + G.d = 3 ∧ (G.a + G.d) * (G.a + G.d) - 4 = 5 := by decide

/-- ★★★★ **Two reflections compose to the golden boost.**  `A`, `B` are involutive reflections
    (`A² = B² = I`, `det = −1`); their product is the golden iterator `G` (`det = +1`), which is
    hyperbolic (`trace 3 > 2`, `disc 5 > 0`).  Together with the elliptic `S = N · R`
    (`FoldReflections`, `|tr| < 2`, rotation), this exhibits the elliptic/hyperbolic split as the two
    faces of one frame — product of two reflections — selected by `|trace|` against `2`. -/
theorem two_reflections_compose_to_golden_boost :
    (mul A A = I2 ∧ mul B B = I2)
    ∧ (A.a * A.d - A.b * A.c = -1 ∧ B.a * B.d - B.b * B.c = -1)
    ∧ mul A B = G
    ∧ (G.a * G.d - G.b * G.c = 1 ∧ G.a + G.d = 3 ∧ (G.a + G.d) * (G.a + G.d) - 4 = 5) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicBoost
