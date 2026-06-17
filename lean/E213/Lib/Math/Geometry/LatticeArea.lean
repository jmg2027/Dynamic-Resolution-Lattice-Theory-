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

open E213.Lib.Math.Geometry.StewartTheorem (Pt sq)
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

/-! ## §2 — bridge to squared distances: Lagrange, law of cosines, Cayley–Menger -/

/-- Dot product of the displacement vectors `B−A` and `C−A`. -/
def dotAt (A B C : Pt) : Int := (B.1 - A.1) * (C.1 - A.1) + (B.2 - A.2) * (C.2 - A.2)

/-- ★★★ **2D Lagrange identity**: `area2² = AB²·AC² − ((B−A)·(C−A))²` — the squared signed area
    equals the Gram determinant `|u|²|v|² − (u·v)²` (`u×v` squared). -/
theorem area2_sq_eq_gram (A B C : Pt) :
    area2 A B C * area2 A B C = sq A B * sq A C - dotAt A B C * dotAt A B C := by
  show ((B.1-A.1)*(C.2-A.2) - (B.2-A.2)*(C.1-A.1)) * ((B.1-A.1)*(C.2-A.2) - (B.2-A.2)*(C.1-A.1))
      = ((A.1-B.1)*(A.1-B.1)+(A.2-B.2)*(A.2-B.2)) * ((A.1-C.1)*(A.1-C.1)+(A.2-C.2)*(A.2-C.2))
        - ((B.1-A.1)*(C.1-A.1)+(B.2-A.2)*(C.2-A.2)) * ((B.1-A.1)*(C.1-A.1)+(B.2-A.2)*(C.2-A.2))
  ring_intZ

/-- ★★ **Law of cosines** (squared-distance form): `BC² = AB² + AC² − 2·((B−A)·(C−A))`. -/
theorem law_of_cosines (A B C : Pt) :
    sq B C = sq A B + sq A C - 2 * dotAt A B C := by
  show (B.1-C.1)*(B.1-C.1)+(B.2-C.2)*(B.2-C.2)
      = ((A.1-B.1)*(A.1-B.1)+(A.2-B.2)*(A.2-B.2)) + ((A.1-C.1)*(A.1-C.1)+(A.2-C.2)*(A.2-C.2))
        - 2 * ((B.1-A.1)*(C.1-A.1)+(B.2-A.2)*(C.2-A.2))
  ring_intZ

/-- Abstract assembly: from the Gram form `a² = x·y − d²` and the cosine form `z = x+y−2d`,
    `4·a² = 4·x·y − (x+y−z)²` (the Cayley–Menger shape in `x = AB², y = AC², z = BC²`). -/
private theorem cayley_menger_abstract (x y z d a : Int)
    (h1 : a * a = x * y - d * d) (h2 : z = x + y - 2 * d) :
    4 * (a * a) = 4 * (x * y) - (x + y - z) * (x + y - z) := by
  rw [h1, h2]; ring_intZ

/-- ★★★ **Cayley–Menger / Heron-squared identity**: `16·Area² = 4·AB²·AC² − (AB²+AC²−BC²)²`,
    i.e. `4·area2² = 4·AB²·AC² − (AB²+AC²−BC²)²` (since `area2 = 2·Area`).

    The integer-coordinate bridge between the signed area `area2` and the squared side lengths
    `sq`.  Assembled from `area2_sq_eq_gram` (Lagrange) + `law_of_cosines` via the abstract
    Cayley–Menger step — sidestepping the degree-8 blow-up that defeats `ring_intZ` directly. -/
theorem cayley_menger (A B C : Pt) :
    4 * (area2 A B C * area2 A B C)
      = 4 * (sq A B * sq A C) - (sq A B + sq A C - sq B C) * (sq A B + sq A C - sq B C) :=
  cayley_menger_abstract (sq A B) (sq A C) (sq B C) (dotAt A B C) (area2 A B C)
    (area2_sq_eq_gram A B C) (law_of_cosines A B C)

/-! ## §3 — behaviour under linear maps: the determinant scales area -/

/-- The linear map `(x,y) ↦ (p·x+q·y, r·x+s·y)` applied to a point. -/
def linMap (p q r s : Int) (P : Pt) : Pt := (p * P.1 + q * P.2, r * P.1 + s * P.2)

/-- ★★★ **Signed area scales by the determinant** under a linear map:
    `area2 (M·A) (M·B) (M·C) = det(M) · area2 A B C` with `M = [[p,q],[r,s]]`, `det = p·s − q·r`.

    In particular **`SL₂(ℤ)` (and `GL₂(ℤ)`, `det = ±1`) preserves lattice area** — the geometric
    root of the modular group's action on the lattice. -/
theorem area2_linMap (p q r s : Int) (A B C : Pt) :
    area2 (linMap p q r s A) (linMap p q r s B) (linMap p q r s C)
      = (p * s - q * r) * area2 A B C := by
  show ((p*B.1+q*B.2)-(p*A.1+q*A.2))*((r*C.1+s*C.2)-(r*A.1+s*A.2))
      - ((r*B.1+s*B.2)-(r*A.1+s*A.2))*((p*C.1+q*C.2)-(p*A.1+q*A.2))
    = (p*s - q*r) * ((B.1-A.1)*(C.2-A.2) - (B.2-A.2)*(C.1-A.1))
  ring_intZ

/-- A unimodular map (`det = 1`, e.g. any element of `SL₂(ℤ)`) preserves signed area exactly. -/
theorem area2_unimodular (p q r s : Int) (hdet : p * s - q * r = 1) (A B C : Pt) :
    area2 (linMap p q r s A) (linMap p q r s B) (linMap p q r s C) = area2 A B C := by
  rw [area2_linMap, hdet, one_mulZ]

/-- Smoke: `3-4-5` right triangle `A=(0,0)`, `B=(3,0)`, `C=(0,4)`.
    `area2 = 12` (Area `6`), `AB²=9`, `AC²=16`, `BC²=25`: `4·144 = 4·9·16 − (9+16−25)² = 576`. -/
theorem cayley_menger_smoke :
    4 * (area2 (0, 0) (3, 0) (0, 4) * area2 (0, 0) (3, 0) (0, 4))
      = 4 * (sq (0, 0) (3, 0) * sq (0, 0) (0, 4))
        - (sq (0, 0) (3, 0) + sq (0, 0) (0, 4) - sq (3, 0) (0, 4))
          * (sq (0, 0) (3, 0) + sq (0, 0) (0, 4) - sq (3, 0) (0, 4)) := by decide

end E213.Lib.Math.Geometry.LatticeArea
