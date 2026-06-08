import E213.Lib.Math.Algebra.Linalg213.CayleyHamilton

/-!
# Linalg213 — the triangular determinant `det = Π Mᵢᵢ`

A triangular matrix has determinant the product of its diagonal.  **Lower**-triangular
(`M i j = 0` for `i < j`): row-`0` cofactor expansion peels `M₀₀` — the rest of row `0` is zero —
and the `(0,0)`-minor is again lower-triangular, so the diagonal product accumulates.  **Upper**-
triangular (`M i j = 0` for `j < i`, the dual): row `0` is *not* mostly zero, so expand along the
**last** row instead (`Laplace.cofactor_row_i` at `k = n`) — only `M n n` survives, sign
`(−1)^(n+n)=1`, and the `(n,n)`-minor is again upper-triangular.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.DetTriangular

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota sumZ)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_map' map_eq_of_mem lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.DetN (det cofSum minor colShift altSign altSign_add)
open E213.Lib.Math.Algebra.Linalg213.Laplace
  (minorAt cofactor_row_i altSign_self sumZ_append map_append')
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton (add_zero' one_mul' mul_zero' matId sumZ_map_zero)

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
          rw [E213.Lib.Math.Algebra.Linalg213.Laplace.map_append']
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
    apply E213.Lib.Math.Algebra.Linalg213.PermClosure.map_eq_of_mem
    intro a _
    show minor M 0 a a = M (a + 1) (a + 1)
    rw [show minor M 0 a a = M (a + 1) (colShift 0 a) from rfl, show colShift 0 a = a + 1 from rfl]

/-- `prodZ` of a constant-`1` map is `1`. -/
theorem prodZ_map_one {α : Type} : ∀ (L : List α), prodZ (L.map (fun _ => (1 : Int))) = 1
  | []     => rfl
  | _ :: l => by
    show (1 : Int) * prodZ (l.map (fun _ => (1 : Int))) = 1
    rw [prodZ_map_one l, one_mul']

/-- ★ **The identity matrix has determinant `1`** (it is lower-triangular with unit diagonal). -/
theorem det_matId (n : Nat) : det n matId = 1 := by
  rw [det_lower_triangular n matId (fun i j hij => by
        show (if i = j then (1 : Int) else 0) = 0
        rw [if_neg (Nat.ne_of_lt hij)]),
      map_eq_of_mem (fun i => matId i i) (fun _ => (1 : Int)) (fun i _ => by
        show (if i = i then (1 : Int) else 0) = 1
        rw [if_pos rfl]),
      prodZ_map_one]

/-! ## The upper-triangular determinant (dual: last-row cofactor expansion)

An upper-triangular matrix (`M i j = 0` for `j < i` — zero **below** the diagonal) has the same
determinant `Π Mᵢᵢ`.  Row-`0` expansion does not collapse here (row `0` is the full first row), so
expand along the **last** row instead (`Laplace.cofactor_row_i` at `k = n`): the last row of an
`(n+1)×(n+1)` upper-triangular matrix is `0,…,0,M n n`, so only the `j = n` term survives, with
sign `(−1)^(n+n) = 1`, and the `(n,n)`-minor is again upper-triangular. -/

/-- `prodZ` over a snoc: `prodZ (L ++ [x]) = prodZ L · x`. -/
theorem prodZ_snoc : ∀ (L : List Int) (x : Int), prodZ (L ++ [x]) = prodZ L * x
  | [],     x => by
    show prodZ [x] = prodZ ([] : List Int) * x
    rw [prodZ_singleton]; show x = 1 * x; rw [one_mul']
  | a :: l, x => by
    show a * prodZ (l ++ [x]) = (a * prodZ l) * x
    rw [prodZ_snoc l x, E213.Meta.Int213.mul_assoc]

/-- The `(n,n)`-minor of an upper-triangular matrix is upper-triangular (its row/column index
    `(if i<n then i else i+1, colShift n j)` keeps the column strictly below the row when `j < i`). -/
theorem minorAt_nn_upperTri {M : Nat → Nat → Int} (hM : ∀ i j, j < i → M i j = 0) (n : Nat) :
    ∀ i j, j < i → minorAt n n M i j = 0 := by
  intro i j hji
  show M (if i < n then i else i + 1) (colShift n j) = 0
  have hcol : colShift n j < (if i < n then i else i + 1) := by
    show (if j < n then j else j + 1) < (if i < n then i else i + 1)
    by_cases hi : i < n
    · rw [if_pos hi, if_pos (Nat.lt_trans hji hi)]; exact hji
    · rw [if_neg hi]
      by_cases hj : j < n
      · rw [if_pos hj]; exact Nat.lt_succ_of_lt hji
      · rw [if_neg hj]; exact Nat.succ_lt_succ hji
  exact hM _ _ hcol

/-- On the diagonal (index `< n`), the `(n,n)`-minor agrees with `M`. -/
theorem minorAt_nn_diag (M : Nat → Nat → Int) (n a : Nat) (ha : a < n) :
    minorAt n n M a a = M a a := by
  show M (if a < n then a else a + 1) (colShift n a) = M a a
  rw [if_pos ha]; show M a (if a < n then a else a + 1) = M a a; rw [if_pos ha]

/-- Last-row cofactor expansion of an upper-triangular matrix collapses to the lead term:
    `det (n+1) M = M n n · det n (minor at (n,n))`. -/
theorem cofExpand_lastRow (n : Nat) (M : Nat → Nat → Int) (hM : ∀ i j, j < i → M i j = 0) :
    det (n + 1) M = M n n * det n (minorAt n n M) := by
  rw [cofactor_row_i M n n (Nat.lt_succ_self n)]
  show sumZ ((iota n ++ [n]).map (fun j => altSign (n + j) * M n j * det n (minorAt n j M)))
     = M n n * det n (minorAt n n M)
  rw [map_append' (fun j => altSign (n + j) * M n j * det n (minorAt n j M)) (iota n) [n],
      sumZ_append,
      map_eq_of_mem (fun j => altSign (n + j) * M n j * det n (minorAt n j M))
        (fun _ => (0 : Int)) (fun j hj => by
          show altSign (n + j) * M n j * det n (minorAt n j M) = 0
          rw [hM n j (lt_of_mem_iota hj), mul_zero', E213.Meta.Int213.zero_mul]),
      sumZ_map_zero, E213.Meta.Int213.zero_add]
  show altSign (n + n) * M n n * det n (minorAt n n M) + 0 = M n n * det n (minorAt n n M)
  rw [add_zero', altSign_add, altSign_self, one_mul']

/-- ★★ **The upper-triangular determinant is the diagonal product.**  For `M i j = 0` whenever
    `j < i`, `det n M = Π_{i<n} M i i` — the dual of `det_lower_triangular`. -/
theorem det_upper_triangular : ∀ (n : Nat) (M : Nat → Nat → Int), (∀ i j, j < i → M i j = 0) →
    det n M = prodZ ((iota n).map (fun i => M i i))
  | 0,     _, _  => rfl
  | n + 1, M, hM => by
    rw [cofExpand_lastRow n M hM,
        det_upper_triangular n (minorAt n n M) (minorAt_nn_upperTri hM n),
        map_eq_of_mem (fun i => minorAt n n M i i) (fun i => M i i)
          (fun a ha => minorAt_nn_diag M n a (lt_of_mem_iota ha))]
    show M n n * prodZ ((iota n).map (fun i => M i i))
       = prodZ ((iota n ++ [n]).map (fun i => M i i))
    rw [map_append' (fun i => M i i) (iota n) [n]]
    show M n n * prodZ ((iota n).map (fun i => M i i))
       = prodZ ((iota n).map (fun i => M i i) ++ [M n n])
    rw [prodZ_snoc]
    show M n n * prodZ ((iota n).map (fun i => M i i))
       = prodZ ((iota n).map (fun i => M i i)) * M n n
    rw [E213.Meta.Int213.mul_comm]

/-! ## The diagonal determinant (a corollary: diagonal ⟹ both triangular) -/

/-- ★ **The diagonal determinant is the diagonal product.**  A diagonal matrix (`M i j = 0`
    whenever `i ≠ j`) is in particular lower-triangular, so `det n M = Π_{i<n} Mᵢᵢ`. -/
theorem det_diagonal (n : Nat) (M : Nat → Nat → Int) (hd : ∀ i j, i ≠ j → M i j = 0) :
    det n M = prodZ ((iota n).map (fun i => M i i)) :=
  det_lower_triangular n M (fun i j hij => hd i j (Nat.ne_of_lt hij))

/-- ★ **The determinant of `diag(d₀,…,d_{n-1})` is `Π dᵢ`.**  The matrix `fun i j => if i = j
    then d i else 0`. -/
theorem det_diag_fun (n : Nat) (d : Nat → Int) :
    det n (fun i j => if i = j then d i else 0) = prodZ ((iota n).map d) := by
  rw [det_diagonal n (fun i j => if i = j then d i else 0)
        (fun i j hij => by show (if i = j then d i else 0) = 0; rw [if_neg hij]),
      map_eq_of_mem (fun i => (if i = i then d i else 0)) d
        (fun i _ => by show (if i = i then d i else 0) = d i; rw [if_pos rfl])]

end E213.Lib.Math.Algebra.Linalg213.DetTriangular
