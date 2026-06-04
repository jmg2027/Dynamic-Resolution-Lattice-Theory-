import E213.Lib.Math.Linalg213.CayleyHamilton

/-!
# Linalg213 — the triangular determinant `det = Π Mᵢᵢ`

A lower-triangular matrix (`M i j = 0` for `i < j`) has determinant the product of its diagonal.
Row-`0` cofactor expansion (the `DetN.det` recursion) peels `M₀₀` — the rest of row `0` is zero —
and the `(0,0)`-minor is again lower-triangular, so the diagonal product accumulates.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.DetTriangular

open E213.Lib.Math.Linalg213.Permutation (iota)
open E213.Lib.Math.Linalg213.PermClosure (map_map')
open E213.Lib.Math.Linalg213.DetN (det cofSum minor colShift altSign)
open E213.Lib.Math.Linalg213.CayleyHamilton (add_zero' one_mul' mul_zero')

/-- Product of an `Int` list. -/
def prodZ : List Int → Int
  | []     => 1
  | a :: l => a * prodZ l

/-- `prodZ` of a singleton. -/
theorem prodZ_singleton (x : Int) : prodZ [x] = x := by
  show x * prodZ ([] : List Int) = x
  show x * 1 = x
  rw [E213.Meta.Int213.mul_one]

/-- `iota` peeled from the **front**: `iota (n+1) = 0 :: (iota n).map succ`. -/
theorem iota_cons : ∀ (n : Nat), iota (n + 1) = 0 :: (iota n).map Nat.succ
  | 0     => rfl
  | n + 1 => by
    show iota (n + 1) ++ [n + 1] = 0 :: ((iota n ++ [n]).map Nat.succ)
    rw [iota_cons n,
        show (iota n ++ [n]).map Nat.succ = (iota n).map Nat.succ ++ [n + 1] from by
          rw [E213.Lib.Math.Linalg213.Laplace.map_append']
          rfl]
    rfl

/-- The cofactor sum of a matrix whose first row is `M₀₀, 0, 0, …` collapses to the single
    `M₀₀·det(minor M 0)` term. -/
theorem cofSum_lowerTri (n : Nat) (M : Nat → Nat → Int) (hz : ∀ j, 0 < j → M 0 j = 0) :
    ∀ (c : Nat), cofSum (det n) M (c + 1) = M 0 0 * det n (minor M 0)
  | 0     => by
    show cofSum (det n) M 0 + altSign 0 * M 0 0 * det n (minor M 0) = M 0 0 * det n (minor M 0)
    show (0 : Int) + 1 * M 0 0 * det n (minor M 0) = M 0 0 * det n (minor M 0)
    rw [E213.Meta.Int213.zero_add, one_mul']
  | c + 1 => by
    show cofSum (det n) M (c + 1) + altSign (c + 1) * M 0 (c + 1) * det n (minor M (c + 1))
       = M 0 0 * det n (minor M 0)
    rw [hz (c + 1) (Nat.succ_pos c), mul_zero', E213.Meta.Int213.zero_mul, add_zero',
        cofSum_lowerTri n M hz c]

/-- The `(0,0)`-minor of a lower-triangular matrix is lower-triangular, with diagonal shifted. -/
theorem minor0_lowerTri {M : Nat → Nat → Int} (hM : ∀ i j, i < j → M i j = 0) :
    ∀ i j, i < j → minor M 0 i j = 0 := by
  intro i j hij
  show M (i + 1) (colShift 0 j) = 0
  rw [show colShift 0 j = j + 1 from rfl]
  exact hM (i + 1) (j + 1) (Nat.succ_lt_succ hij)

/-- ★★ **The lower-triangular determinant is the diagonal product.**  For `M i j = 0` whenever
    `i < j`, `det n M = Π_{i<n} M i i`. -/
theorem det_lower_triangular : ∀ (n : Nat) (M : Nat → Nat → Int), (∀ i j, i < j → M i j = 0) →
    det n M = prodZ ((iota n).map (fun i => M i i))
  | 0,     _, _  => rfl
  | n + 1, M, hM => by
    show cofSum (det n) M (n + 1) = prodZ ((iota (n + 1)).map (fun i => M i i))
    rw [cofSum_lowerTri n M (fun j hj => hM 0 j hj) n,
        det_lower_triangular n (minor M 0) (minor0_lowerTri hM),
        iota_cons n,
        show (0 :: (iota n).map Nat.succ).map (fun i => M i i)
           = M 0 0 :: ((iota n).map Nat.succ).map (fun i => M i i) from rfl,
        map_map' Nat.succ (fun i => M i i)]
    show M 0 0 * prodZ ((iota n).map (fun i => minor M 0 i i))
       = M 0 0 * prodZ ((iota n).map (fun a => M (a + 1) (a + 1)))
    apply congrArg (fun z => M 0 0 * z)
    apply congrArg prodZ
    apply E213.Lib.Math.Linalg213.PermClosure.map_eq_of_mem
    intro a _
    show minor M 0 a a = M (a + 1) (a + 1)
    rw [show minor M 0 a a = M (a + 1) (colShift 0 a) from rfl, show colShift 0 a = a + 1 from rfl]

end E213.Lib.Math.Linalg213.DetTriangular
