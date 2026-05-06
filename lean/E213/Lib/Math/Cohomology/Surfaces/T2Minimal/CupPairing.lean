import E213.Lib.Math.Cohomology.Surfaces.T2Minimal
import E213.Lib.Math.NatHelpers.IntHelpers

/-!
# Cup-pairing on H¹(T²; ℤ) — hyperbolic intersection form

The cup-pairing on the 2-torus,
  ⌣ : H¹(T²; ℤ) × H¹(T²; ℤ) → H²(T²; ℤ)
in the standard basis `{a, b}` of H¹ is the **symmetric hyperbolic
form** with matrix `[[0, 1], [1, 0]]`:

  α ⌣ β  =  α(a)·β(b) + α(b)·β(a)

ℤ-symmetric matrix `M = [[0,1],[1,0]]` has characteristic
polynomial `λ² − 1`, eigenvalues `±1`, signature `(1, 1)`.

The signature `(1, 1)` matches the Hodge Index Theorem prediction
`(1, ρ − 1)` with Picard rank `ρ = 2` for T² (two algebraic loops).

STRICT ∅-AXIOM (all by `decide` on finite enumerations).
-/

namespace E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing

open E213.Lib.Math.Cohomology.Surfaces.T2Minimal

/-- Symmetric cup-pairing on `C1 × C1 → C2`.
    `(α ⌣ β)(f) = α(a)·β(b) + α(b)·β(a)`. -/
def cup (α β : C1) : C2 :=
  fun _ => α Cell1.a * β Cell1.b + α Cell1.b * β Cell1.a

/-- Standard basis vector for the `a`-loop. -/
def basis_a : C1 := fun
  | Cell1.a => 1
  | Cell1.b => 0

/-- Standard basis vector for the `b`-loop. -/
def basis_b : C1 := fun
  | Cell1.a => 0
  | Cell1.b => 1

end E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing

namespace E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing

open E213.Lib.Math.Cohomology.Surfaces.T2Minimal

/-! ## §2 — Matrix entries -/

/-- Matrix entry: `(basis_a ⌣ basis_a)(f) = 0`. -/
theorem cup_aa : cup basis_a basis_a Cell2.f = 0 := by decide

/-- Matrix entry: `(basis_a ⌣ basis_b)(f) = 1`. -/
theorem cup_ab : cup basis_a basis_b Cell2.f = 1 := by decide

/-- Matrix entry: `(basis_b ⌣ basis_a)(f) = 1`.  Symmetric. -/
theorem cup_ba : cup basis_b basis_a Cell2.f = 1 := by decide

/-- Matrix entry: `(basis_b ⌣ basis_b)(f) = 0`. -/
theorem cup_bb : cup basis_b basis_b Cell2.f = 0 := by decide

/-- Cup is symmetric: `α ⌣ β = β ⌣ α`. -/
theorem cup_symm (α β : C1) : cup α β = cup β α := by
  funext _
  show α Cell1.a * β Cell1.b + α Cell1.b * β Cell1.a
     = β Cell1.a * α Cell1.b + β Cell1.b * α Cell1.a
  have h1 : α Cell1.a * β Cell1.b = β Cell1.b * α Cell1.a := Int.mul_comm _ _
  have h2 : α Cell1.b * β Cell1.a = β Cell1.a * α Cell1.b := Int.mul_comm _ _
  rw [h1, h2, Int.add_comm]

end E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing
