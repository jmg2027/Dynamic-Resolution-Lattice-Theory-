import E213.Meta.Int213.Core

/-!
# Linalg213 — the `n×n` determinant over `ℤ` (cofactor expansion)

The general determinant, the foundational gap identified for the **C-finite Hadamard
product** (its annihilator is a resultant = a determinant) and for the **Casoratian
rank** characterization.  `Gap/Determinant.lean` had only the `2×2`/`3×3` closed forms;
this is the recursive `n×n` form over `ℤ`.

A matrix is a function `M : Nat → Nat → Int` (`M i j` = row `i`, column `j`); the size
`n` is carried separately.  `det n M` expands along the first row:

> `det (n+1) M = Σ_{j=0}^{n} (−1)ʲ · M 0 j · det n (minor M j)`

where `minor M j` drops row `0` and column `j`.  Base `det 0 _ = 1`.

All ∅-axiom (over `Int213`).
-/

namespace E213.Lib.Math.Linalg213.DetN

open E213.Meta.Int213 (add_comm add_assoc mul_comm mul_assoc mul_add add_mul neg_mul mul_one zero_add)

/-- The alternating sign `(−1)ⁿ` over `ℤ` (core-free). -/
def altSign : Nat → Int
  | 0   => 1
  | n+1 => -(altSign n)

/-- The `(0,j)`-minor: drop row `0` and column `j`. -/
def minor (M : Nat → Nat → Int) (j : Nat) : Nat → Nat → Int :=
  fun i l => M (i + 1) (if l < j then l else l + 1)

/-- Cofactor sum along the first row, over the first `c` columns:
    `Σ_{j<c} (−1)ʲ · M 0 j · detN (minor M j)`. -/
def cofSum (detN : (Nat → Nat → Int) → Int) (M : Nat → Nat → Int) : Nat → Int
  | 0   => 0
  | c+1 => cofSum detN M c + altSign c * M 0 c * detN (minor M c)

/-- The `n×n` determinant, first-row cofactor (Laplace) expansion. -/
def det : Nat → (Nat → Nat → Int) → Int
  | 0,   _ => 1
  | n+1, M => cofSum (det n) M (n + 1)

/-! ## §1 — small-size sanity -/

/-- `1×1`: `det = M 0 0`. -/
theorem det_one (M : Nat → Nat → Int) : det 1 M = M 0 0 := by
  show cofSum (det 0) M 1 = M 0 0
  show (0 : Int) + altSign 0 * M 0 0 * det 0 (minor M 0) = M 0 0
  show (0 : Int) + 1 * M 0 0 * 1 = M 0 0
  rw [Int.one_mul, mul_one, zero_add]

/-- `2×2`: `det = M00·M11 − M01·M10`. -/
theorem det_two (M : Nat → Nat → Int) :
    det 2 M = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  show cofSum (det 1) M 2 = M 0 0 * M 1 1 - M 0 1 * M 1 0
  show ((0 : Int) + altSign 0 * M 0 0 * det 1 (minor M 0))
        + altSign 1 * M 0 1 * det 1 (minor M 1)
     = M 0 0 * M 1 1 - M 0 1 * M 1 0
  rw [det_one (minor M 0), det_one (minor M 1)]
  show ((0 : Int) + 1 * M 0 0 * minor M 0 0 0) + (-(1)) * M 0 1 * minor M 1 0 0
     = M 0 0 * M 1 1 - M 0 1 * M 1 0
  show ((0 : Int) + 1 * M 0 0 * M 1 1) + (-(1)) * M 0 1 * M 1 0
     = M 0 0 * M 1 1 - M 0 1 * M 1 0
  rw [Int.one_mul, neg_mul, Int.one_mul, neg_mul, zero_add, Int.sub_eq_add_neg]

end E213.Lib.Math.Linalg213.DetN
