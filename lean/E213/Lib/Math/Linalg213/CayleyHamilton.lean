import E213.Lib.Math.Linalg213.Laplace

/-!
# Linalg213 — integer Cayley–Hamilton (toward the C-finite Hadamard product)

With the adjugate identity `M · adj M = det M · I` (`Laplace`) in hand, the matrix ring
infrastructure (`matMul` associativity, `matAdd`, the identity, powers) and the telescoping
that yields `χ_M(M) = 0`.

This file starts with the finite-sum **Fubini** (double-sum swap) that powers `matMul`
associativity.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.CayleyHamilton

open E213.Lib.Math.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Linalg213.PermClosure (sumZ_map_add sumZ_map_smul map_eq_of_mem)
open E213.Lib.Math.Linalg213.Laplace (sumZ_append matMul map_append')

/-! ## §1 — finite-sum Fubini -/

/-- The sum of a constant-`0` map is `0`. -/
theorem sumZ_map_zero {α : Type} : ∀ (L : List α), sumZ (L.map (fun _ => (0 : Int))) = 0
  | []     => rfl
  | _ :: l => by
    show (0 : Int) + sumZ (l.map (fun _ => (0 : Int))) = 0
    rw [sumZ_map_zero l, E213.Meta.Int213.zero_add]

/-- ★ **Fubini**: a double sum may be swapped. -/
theorem sumZ_swap {α β : Type} (g : α → β → Int) : ∀ (L1 : List α) (L2 : List β),
    sumZ (L1.map (fun j => sumZ (L2.map (fun k => g j k))))
      = sumZ (L2.map (fun k => sumZ (L1.map (fun j => g j k))))
  | [],      L2 => (sumZ_map_zero L2).symm
  | j :: js, L2 => by
    show sumZ (L2.map (fun k => g j k)) + sumZ (js.map (fun j => sumZ (L2.map (fun k => g j k))))
       = sumZ (L2.map (fun k => sumZ ((j :: js).map (fun j => g j k))))
    rw [sumZ_swap g js L2, ← sumZ_map_add]
    apply congrArg sumZ
    apply map_eq_of_mem
    intro k _
    rfl

/-- Right scalar pulls out of `sumZ`. -/
theorem sumZ_map_smul_right {α : Type} (c : Int) (f : α → Int) : ∀ (L : List α),
    sumZ (L.map f) * c = sumZ (L.map (fun x => f x * c))
  | []     => by show (0 : Int) * c = 0; rw [E213.Meta.Int213.zero_mul]
  | a :: l => by
    show (f a + sumZ (l.map f)) * c = f a * c + sumZ (l.map (fun x => f x * c))
    rw [E213.Meta.Int213.add_mul, sumZ_map_smul_right c f l]

/-! ## §2 — matrix multiplication is associative -/

/-- ★★ **`matMul` is associative** (pointwise). -/
theorem matMul_assoc (n : Nat) (M N P : Nat → Nat → Int) (i l : Nat) :
    matMul n M (matMul n N P) i l = matMul n (matMul n M N) P i l := by
  show sumZ ((iota n).map (fun j => M i j * matMul n N P j l))
     = sumZ ((iota n).map (fun k => matMul n M N i k * P k l))
  rw [map_eq_of_mem (fun j => M i j * matMul n N P j l)
        (fun j => sumZ ((iota n).map (fun k => M i j * (N j k * P k l))))
        (fun j _ => by
          show M i j * sumZ ((iota n).map (fun k => N j k * P k l))
             = sumZ ((iota n).map (fun k => M i j * (N j k * P k l)))
          rw [← sumZ_map_smul]),
      sumZ_swap (fun j k => M i j * (N j k * P k l)),
      map_eq_of_mem (fun k => sumZ ((iota n).map (fun j => M i j * (N j k * P k l))))
        (fun k => matMul n M N i k * P k l)
        (fun k _ => by
          show sumZ ((iota n).map (fun j => M i j * (N j k * P k l)))
             = sumZ ((iota n).map (fun j => M i j * N j k)) * P k l
          rw [sumZ_map_smul_right]
          apply congrArg sumZ
          apply map_eq_of_mem
          intro j _
          rw [E213.Meta.Int213.mul_assoc])]

/-! ## §3 — the matrix ring: identity, addition, scalar, and the identity laws -/

/-- `a + 0 = a` over `ℤ` (propext-free, `Int213` has no `add_zero`). -/
theorem add_zero' (a : Int) : a + 0 = a := by
  rw [E213.Meta.Int213.add_comm, E213.Meta.Int213.zero_add]

/-- `1 * a = a` over `ℤ`. -/
theorem one_mul' (a : Int) : 1 * a = a := by
  rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.mul_one]

/-- `a * 0 = 0` over `ℤ`. -/
theorem mul_zero' (a : Int) : a * 0 = 0 := by
  rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.zero_mul]

/-- `sumZ` of a singleton. -/
theorem sumZ_singleton (x : Int) : sumZ [x] = x := add_zero' x

/-- The `n×n` identity matrix (Kronecker delta). -/
def matId : Nat → Nat → Int := fun i j => if i = j then 1 else 0

/-- Entrywise matrix addition. -/
def matAdd (M N : Nat → Nat → Int) : Nat → Nat → Int := fun i j => M i j + N i j

/-- Entrywise negation. -/
def matNeg (M : Nat → Nat → Int) : Nat → Nat → Int := fun i j => - M i j

/-- The zero matrix. -/
def matZero : Nat → Nat → Int := fun _ _ => 0

/-- Scalar multiple of a matrix. -/
def matScalar (c : Int) (M : Nat → Nat → Int) : Nat → Nat → Int := fun i j => c * M i j

/-- **Kronecker-delta sum (vanishing range)**: when `i ≥ n`, every index `k < n` of
    `iota n` differs from `i`, so the delta sum is `0`. -/
theorem sumZ_iota_delta_ge (f : Nat → Int) (i : Nat) : ∀ (n : Nat), n ≤ i →
    sumZ ((iota n).map (fun k => if i = k then f k else 0)) = 0
  | 0,     _ => rfl
  | n + 1, h => by
    rw [show iota (n + 1) = iota n ++ [n] from rfl, map_append', sumZ_append,
        show List.map (fun k => if i = k then f k else 0) [n] = [if i = n then f n else 0] from rfl,
        sumZ_singleton, sumZ_iota_delta_ge f i n (Nat.le_of_succ_le h),
        if_neg (Nat.ne_of_gt h), E213.Meta.Int213.zero_add]

/-- ★ **Kronecker-delta sum (hit)**: summing `if i = k then f k else 0` over `iota n`
    picks out `f i` exactly when `i < n`. -/
theorem sumZ_iota_delta_lt (f : Nat → Int) (i : Nat) : ∀ (n : Nat), i < n →
    sumZ ((iota n).map (fun k => if i = k then f k else 0)) = f i
  | n + 1, hi => by
    rw [show iota (n + 1) = iota n ++ [n] from rfl, map_append', sumZ_append,
        show List.map (fun k => if i = k then f k else 0) [n] = [if i = n then f n else 0] from rfl,
        sumZ_singleton]
    by_cases h : i = n
    · subst h
      rw [sumZ_iota_delta_ge f i i (Nat.le_refl i), if_pos rfl, E213.Meta.Int213.zero_add]
    · rw [sumZ_iota_delta_lt f i n (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) h),
          if_neg h, add_zero']

/-- ★ **Left identity**: `matId · M = M` (at any row `i < n`). -/
theorem matMul_id_left (n : Nat) (M : Nat → Nat → Int) (i j : Nat) (hi : i < n) :
    matMul n matId M i j = M i j := by
  show sumZ ((iota n).map (fun k => matId i k * M k j)) = M i j
  rw [map_eq_of_mem (fun k => matId i k * M k j) (fun k => if i = k then M k j else 0)
        (fun k _ => by
          show (if i = k then (1 : Int) else 0) * M k j = if i = k then M k j else 0
          by_cases h : i = k
          · rw [if_pos h, if_pos h]; exact one_mul' (M k j)
          · rw [if_neg h, if_neg h]; exact E213.Meta.Int213.zero_mul (M k j)),
      sumZ_iota_delta_lt (fun k => M k j) i n hi]

/-- ★ **Right identity**: `M · matId = M` (at any column `j < n`). -/
theorem matMul_id_right (n : Nat) (M : Nat → Nat → Int) (i j : Nat) (hj : j < n) :
    matMul n M matId i j = M i j := by
  show sumZ ((iota n).map (fun k => M i k * matId k j)) = M i j
  rw [map_eq_of_mem (fun k => M i k * matId k j) (fun k => if j = k then M i k else 0)
        (fun k _ => by
          show M i k * (if k = j then (1 : Int) else 0) = if j = k then M i k else 0
          by_cases h : k = j
          · rw [if_pos h, if_pos h.symm]; exact E213.Meta.Int213.mul_one (M i k)
          · rw [if_neg h, if_neg (fun he => h he.symm)]; exact mul_zero' (M i k)),
      sumZ_iota_delta_lt (fun k => M i k) j n hj]

/-! ## §4 — distributivity, scalar/negation, and matrix powers -/

/-- ★ **Left distributivity**: `(A + B)·C = A·C + B·C`. -/
theorem matMul_addL (n : Nat) (A B C : Nat → Nat → Int) (i j : Nat) :
    matMul n (matAdd A B) C i j = matAdd (matMul n A C) (matMul n B C) i j := by
  show sumZ ((iota n).map (fun k => (A i k + B i k) * C k j))
     = sumZ ((iota n).map (fun k => A i k * C k j)) + sumZ ((iota n).map (fun k => B i k * C k j))
  rw [← sumZ_map_add]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro k _
  exact E213.Meta.Int213.add_mul (A i k) (B i k) (C k j)

/-- ★ **Right distributivity**: `A·(B + C) = A·B + A·C`. -/
theorem matMul_addR (n : Nat) (A B C : Nat → Nat → Int) (i j : Nat) :
    matMul n A (matAdd B C) i j = matAdd (matMul n A B) (matMul n A C) i j := by
  show sumZ ((iota n).map (fun k => A i k * (B k j + C k j)))
     = sumZ ((iota n).map (fun k => A i k * B k j)) + sumZ ((iota n).map (fun k => A i k * C k j))
  rw [← sumZ_map_add]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro k _
  exact E213.Meta.Int213.mul_add (A i k) (B k j) (C k j)

/-- ★ **Left scalar**: `(c • A)·B = c • (A·B)`. -/
theorem matMul_scalarL (n : Nat) (c : Int) (A B : Nat → Nat → Int) (i j : Nat) :
    matMul n (matScalar c A) B i j = matScalar c (matMul n A B) i j := by
  show sumZ ((iota n).map (fun k => c * A i k * B k j)) = c * sumZ ((iota n).map (fun k => A i k * B k j))
  rw [← sumZ_map_smul]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro k _
  exact E213.Meta.Int213.mul_assoc c (A i k) (B k j)

/-- `-0 = 0` over `ℤ`. -/
theorem neg_zero' : -(0 : Int) = 0 :=
  (E213.Meta.Int213.zero_add (-0)).symm.trans (E213.Meta.Int213.add_neg_cancel 0)

/-- Negation pulls out of `sumZ`. -/
theorem sumZ_map_neg {α : Type} (f : α → Int) : ∀ (L : List α),
    sumZ (L.map (fun a => - f a)) = - sumZ (L.map f)
  | []     => neg_zero'.symm
  | a :: l => by
    show - f a + sumZ (l.map (fun a => - f a)) = -(f a + sumZ (l.map f))
    rw [sumZ_map_neg f l, E213.Meta.Int213.neg_add]

/-- ★ **Left negation**: `(-A)·B = -(A·B)`. -/
theorem matMul_negL (n : Nat) (A B : Nat → Nat → Int) (i j : Nat) :
    matMul n (matNeg A) B i j = matNeg (matMul n A B) i j := by
  show sumZ ((iota n).map (fun k => (- A i k) * B k j)) = - sumZ ((iota n).map (fun k => A i k * B k j))
  rw [map_eq_of_mem (fun k => (- A i k) * B k j) (fun k => -(A i k * B k j))
        (fun k _ => E213.Meta.Int213.neg_mul (A i k) (B k j)),
      sumZ_map_neg (fun k => A i k * B k j)]

/-- Matrix power: `M^0 = I`, `M^(k+1) = M · M^k`. -/
def matPow (n : Nat) (M : Nat → Nat → Int) : Nat → (Nat → Nat → Int)
  | 0     => matId
  | k + 1 => matMul n M (matPow n M k)

end E213.Lib.Math.Linalg213.CayleyHamilton
