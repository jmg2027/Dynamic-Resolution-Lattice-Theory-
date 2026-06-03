import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

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

open E213.Meta.Int213 (add_comm add_assoc mul_comm mul_assoc mul_add add_mul neg_mul mul_one zero_add zero_mul)

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

/-! ## §2 — multilinearity in the first row

The cofactor expansion `det (n+1) M = Σ_j (−1)ʲ M 0 j · det n (minor M j)` has cofactors
`det n (minor M j)` that depend only on rows `1…n` (the minor drops row 0).  So `det` is a
**linear functional of the first row** — additive and scalar-homogeneous in it.  (The full
*alternating* property — two equal rows ⟹ `det = 0` — has an irreducible hard core: the
row-0↔row-1 swap is not reducible to the first-row expansion and needs a double expansion.) -/

/-- ★ **`det` respects pointwise matrix equality** (`∅`-axiom; avoids `funext`, which is
    `Quot.sound`-dirty).  The basic congruence for matrix-as-function arguments. -/
theorem det_congr : ∀ (n : Nat) {M M' : Nat → Nat → Int}, (∀ i j, M i j = M' i j) →
    det n M = det n M'
  | 0,   _, _, _ => rfl
  | n+1, M, M', h => by
    have minorEq : ∀ (j i l : Nat), minor M j i l = minor M' j i l :=
      fun j i l => h (i + 1) (if l < j then l else l + 1)
    have cof : ∀ c, cofSum (det n) M c = cofSum (det n) M' c := by
      intro c
      induction c with
      | zero => rfl
      | succ c ih =>
        show cofSum (det n) M c + altSign c * M 0 c * det n (minor M c)
           = cofSum (det n) M' c + altSign c * M' 0 c * det n (minor M' c)
        rw [ih, h 0 c, det_congr n (minorEq c)]
    exact cof (n + 1)

/-- Replace row `0` of `M` by `r`. -/
def setRow0 (r : Nat → Int) (M : Nat → Nat → Int) : Nat → Nat → Int :=
  fun i j => if i = 0 then r j else M i j

/-- The cofactor `det (minor …)` is unchanged by replacing row 0 (the minor drops row 0). -/
theorem detMinor_setRow0 (n : Nat) (r : Nat → Int) (M : Nat → Nat → Int) (j : Nat) :
    det n (minor (setRow0 r M) j) = det n (minor M j) :=
  det_congr n (fun i l => by
    show (if i + 1 = 0 then r (if l < j then l else l + 1) else M (i + 1) (if l < j then l else l + 1))
       = M (i + 1) (if l < j then l else l + 1)
    rw [if_neg (fun h => Nat.noConfusion h)])

/-- Cofactor sum is additive in the first row. -/
theorem cofSum_row0_add (n : Nat) (r1 r2 : Nat → Int) (M : Nat → Nat → Int) : ∀ c,
    cofSum (det n) (setRow0 (fun j => r1 j + r2 j) M) c
      = cofSum (det n) (setRow0 r1 M) c + cofSum (det n) (setRow0 r2 M) c
  | 0   => by show (0 : Int) = 0 + 0; rw [zero_add]
  | c+1 => by
    show cofSum (det n) (setRow0 (fun j => r1 j + r2 j) M) c
           + altSign c * (r1 c + r2 c) * det n (minor (setRow0 (fun j => r1 j + r2 j) M) c)
       = (cofSum (det n) (setRow0 r1 M) c + altSign c * r1 c * det n (minor (setRow0 r1 M) c))
         + (cofSum (det n) (setRow0 r2 M) c + altSign c * r2 c * det n (minor (setRow0 r2 M) c))
    rw [cofSum_row0_add n r1 r2 M c, detMinor_setRow0, detMinor_setRow0, detMinor_setRow0]
    ring_intZ

/-- Cofactor sum is scalar-homogeneous in the first row. -/
theorem cofSum_row0_smul (n : Nat) (a : Int) (r : Nat → Int) (M : Nat → Nat → Int) : ∀ c,
    cofSum (det n) (setRow0 (fun j => a * r j) M) c
      = a * cofSum (det n) (setRow0 r M) c
  | 0   => by show (0 : Int) = a * 0; rw [mul_comm, zero_mul]
  | c+1 => by
    show cofSum (det n) (setRow0 (fun j => a * r j) M) c
           + altSign c * (a * r c) * det n (minor (setRow0 (fun j => a * r j) M) c)
       = a * (cofSum (det n) (setRow0 r M) c + altSign c * r c * det n (minor (setRow0 r M) c))
    rw [cofSum_row0_smul n a r M c, detMinor_setRow0, detMinor_setRow0]
    ring_intZ

/-- ★ **`det` is additive in the first row.** -/
theorem det_row0_add (n : Nat) (r1 r2 : Nat → Int) (M : Nat → Nat → Int) :
    det (n+1) (setRow0 (fun j => r1 j + r2 j) M)
      = det (n+1) (setRow0 r1 M) + det (n+1) (setRow0 r2 M) :=
  cofSum_row0_add n r1 r2 M (n+1)

/-- ★ **`det` is scalar-homogeneous in the first row.** -/
theorem det_row0_smul (n : Nat) (a : Int) (r : Nat → Int) (M : Nat → Nat → Int) :
    det (n+1) (setRow0 (fun j => a * r j) M) = a * det (n+1) (setRow0 r M) :=
  cofSum_row0_smul n a r M (n+1)

end E213.Lib.Math.Linalg213.DetN
