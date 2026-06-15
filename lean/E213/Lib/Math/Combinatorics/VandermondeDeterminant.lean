import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul

/-!
# The Vandermonde determinant `det Vₙ = ∏_{i<j}(xⱼ − xᵢ)` (n = 2, 3; ∅-axiom)

The **matrix determinant** of the Vandermonde matrix `[[1,xᵢ,xᵢ²,…]]` — distinct
from the binomial/convolution Vandermonde *identity* already in the corpus
(`DyadicFSM/FLT/Vandermonde.lean`).  Genuinely absent.

  * **`det2_eq`** : `det [[1,a],[1,b]] = b − a`.
  * ★ **`vanDet3_factored`** : `det [[1,a,a²],[1,b,b²],[1,c,c²]] = (b−a)(c−a)(c−b)`
    (first-row cofactor expansion, closed by `ring_intZ`).
  * **`vanDet3_ne_zero`** : distinct (strictly ordered) points ⟹ nonzero determinant
    (each factor positive, product positive via `mul_pos`) — the basis of
    polynomial-interpolation uniqueness.

All ∅-axiom (`ring_intZ` for the identities; Int213 order for positivity).
-/

namespace E213.Lib.Math.Combinatorics.VandermondeDeterminant

open E213.Meta.Int213.Order
open E213.Meta.Int213.OrderMul

/-- Determinant of `[[1, a], [1, b]]` by the 2×2 rule `ad − bc`. -/
def det2 (a b : Int) : Int := 1 * b - a * 1

/-- **2×2 Vandermonde determinant** `= b − a`. -/
theorem det2_eq (a b : Int) : det2 a b = b - a := by
  unfold det2; ring_intZ

/-- Cofactor (first-row) expansion of the determinant of
    `[[1, a, a²], [1, b, b²], [1, c, c²]]`:
    `1·(b·c² − c·b²) − a·(c² − b²) + a²·(c − b)`. -/
def vanDet3 (a b c : Int) : Int :=
  1 * (b * (c * c) - c * (b * b))
    - a * (1 * (c * c) - 1 * (b * b))
    + (a * a) * (1 * c - 1 * b)

/-- ★ **3×3 Vandermonde determinant** factors as `(b−a)(c−a)(c−b)`. -/
theorem vanDet3_factored (a b c : Int) :
    vanDet3 a b c = (b - a) * (c - a) * (c - b) := by
  unfold vanDet3; ring_intZ

/-- A positive integer is nonzero. -/
theorem ne_zero_of_pos {x : Int} (h : 0 < x) : x ≠ 0 := by
  intro hx
  exact lt_irrefl 0 (hx ▸ h)

/-- Strictly ordered points give a positive determinant (`a < b < c`). -/
theorem vanDet3_pos {a b c : Int} (hab : a < b) (hbc : b < c) :
    0 < vanDet3 a b c := by
  have hba : (0 : Int) < b - a := sub_pos_of_lt hab
  have hcb : (0 : Int) < c - b := sub_pos_of_lt hbc
  have hca : (0 : Int) < c - a := sub_pos_of_lt (lt_trans hab hbc)
  have hprod : 0 < (b - a) * (c - a) * (c - b) :=
    mul_pos (mul_pos hba hca) hcb
  exact (vanDet3_factored a b c) ▸ hprod

/-- Distinct (strictly ordered) points ⟹ nonzero Vandermonde determinant. -/
theorem vanDet3_ne_zero {a b c : Int} (hab : a < b) (hbc : b < c) :
    vanDet3 a b c ≠ 0 :=
  ne_zero_of_pos (vanDet3_pos hab hbc)

end E213.Lib.Math.Combinatorics.VandermondeDeterminant
