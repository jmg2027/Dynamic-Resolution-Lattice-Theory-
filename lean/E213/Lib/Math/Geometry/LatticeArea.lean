import E213.Lib.Math.Geometry.StewartTheorem
import E213.Meta.Int213.Order

/-!
# Signed lattice area, the shoelace formula, and collinearity (∅-axiom)

For integer points the **doubled signed area** of triangle `ABC` is the `2×2` determinant
`(B−A) × (C−A) = (B₁−A₁)(C₂−A₂) − (B₂−A₂)(C₁−A₁)` — an integer (no `½`, no `√`).  This file
collects its named properties, all polynomial identities over `ℤ`:

  * `shoelace` — the determinant equals the symmetric shoelace sum
    `A₁(B₂−C₂) + B₁(C₂−A₂) + C₁(A₂−B₂)`.
  * `area_additivity` — `[PAB] + [PBC] + [PCA] = [ABC]` for any point `P` (triangulation /
    barycentric splitting).
  * `area_translation_invariant`, `area_cyclic`, `area_swap_neg` — symmetry group of the area.
  * `collinear` (defined as doubled area `0`) with `area_zero_of_collinear` and the smoke that a
    degenerate triple has area `0` while a genuine triangle does not.

All ∅-axiom.
-/

namespace E213.Lib.Math.Geometry.LatticeArea

open E213.Lib.Math.Geometry.StewartTheorem (Pt)
open E213.Meta.Int213.PolyIntM
open E213.Meta.Int213 (zero_mul)
open E213.Meta.Int213.Order (sub_self_zero)

/-- The 2D cross product (signed parallelogram area) of two displacement vectors. -/
def cross2 (u v : Pt) : Int := u.1 * v.2 - u.2 * v.1

/-- Doubled signed area of triangle `ABC` — the determinant `(B−A) × (C−A)`. -/
def area2 (A B C : Pt) : Int :=
  (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)

/-- ★★★ **Shoelace formula**: the doubled signed area equals the symmetric cyclic sum
    `A₁(B₂−C₂) + B₁(C₂−A₂) + C₁(A₂−B₂)`. -/
theorem shoelace (A B C : Pt) :
    area2 A B C = A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) := by
  show (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)
      = A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)
  ring_intZ

/-- ★★★ **Signed-area additivity** (triangulation from any point `P`):
    `[PAB] + [PBC] + [PCA] = [ABC]` — the basis of barycentric coordinates. -/
theorem area_additivity (A B C P : Pt) :
    area2 P A B + area2 P B C + area2 P C A = area2 A B C := by
  show ((A.1 - P.1) * (B.2 - P.2) - (A.2 - P.2) * (B.1 - P.1))
      + ((B.1 - P.1) * (C.2 - P.2) - (B.2 - P.2) * (C.1 - P.1))
      + ((C.1 - P.1) * (A.2 - P.2) - (C.2 - P.2) * (A.1 - P.1))
    = (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)
  ring_intZ

/-- **Translation invariance**: shifting all three vertices by `t` leaves the area unchanged. -/
theorem area_translation_invariant (A B C t : Pt) :
    area2 (A.1 + t.1, A.2 + t.2) (B.1 + t.1, B.2 + t.2) (C.1 + t.1, C.2 + t.2) = area2 A B C := by
  show ((B.1 + t.1) - (A.1 + t.1)) * ((C.2 + t.2) - (A.2 + t.2))
      - ((B.2 + t.2) - (A.2 + t.2)) * ((C.1 + t.1) - (A.1 + t.1))
    = (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)
  ring_intZ

/-- **Cyclic invariance**: rotating the vertices preserves the signed area. -/
theorem area_cyclic (A B C : Pt) : area2 A B C = area2 B C A := by
  show (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)
      = (C.1 - B.1) * (A.2 - B.2) - (C.2 - B.2) * (A.1 - B.1)
  ring_intZ

/-- **Orientation flip**: swapping two vertices negates the signed area. -/
theorem area_swap_neg (A B C : Pt) : area2 A B C = -(area2 A C B) := by
  show (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)
      = -((C.1 - A.1) * (B.2 - A.2) - (C.2 - A.2) * (B.1 - A.1))
  ring_intZ

/-- Three points are **collinear** when their doubled signed area vanishes (the displacement
    vectors `B−A`, `C−A` are parallel — zero `2×2` determinant). -/
def Collinear (A B C : Pt) : Prop := area2 A B C = 0

/-- A repeated vertex forces collinearity (`area2 A A C = 0`). -/
theorem collinear_of_eq_fst (A C : Pt) : Collinear A A C := by
  show (A.1 - A.1) * (C.2 - A.2) - (A.2 - A.2) * (C.1 - A.1) = 0
  rw [sub_self_zero A.1, sub_self_zero A.2, zero_mul, zero_mul, sub_self_zero 0]

/-- Smoke: `(0,0),(2,1),(4,2)` are collinear (area `0`); `(0,0),(1,0),(0,1)` is a unit
    right triangle of doubled area `1`. -/
theorem area_smoke :
    area2 (0, 0) (2, 1) (4, 2) = 0 ∧ area2 (0, 0) (1, 0) (0, 1) = 1 := by decide

end E213.Lib.Math.Geometry.LatticeArea
