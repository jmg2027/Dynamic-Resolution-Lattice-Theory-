import E213.Lib.Math.Algebra.Linalg213.DetRowOps
import E213.Lib.Math.Algebra.Linalg213.DetTriangular
import E213.Lib.Math.Algebra.Linalg213.PermSign

/-!
# Linalg213 — the determinant of a permutation matrix is its sign

The two readings of a permutation, identified: `det (permMatrix σ) = psign σ`.  A permutation
value-list `σ` reads as a matrix `permMatrix σ` (row `i` carries its `1` in column `σ i`) and as
a sign `psign σ = (−1)^(inversions σ)`.  The determinant of the one is the other.

The proof reuses the **bubble-sort reduction** already powering `PermSign.psign_mul`: an adjacent
position-swap `swapAt` is a **row swap** of `permMatrix` (`det_swapRows` negates the determinant,
`psign_swapAt` negates the sign), and `descent_of_inv_pos` drives `σ` down to `iota n` where the
matrix is lower-triangular with unit diagonal (`det_lower_triangular`, value `1`) and the sign is
`(−1)^0 = 1`.  Both halves track the *same* sign at every transposition.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.PermMatrixDet

open E213.Lib.Math.Algebra.Linalg213.DetN (det minor det_congr)
open E213.Lib.Math.Algebra.Linalg213.DetRowOps (swapRows det_swapRows)
open E213.Lib.Math.Algebra.Linalg213.DetTriangular (prodZ det_lower_triangular prodZ_map_one)
open E213.Lib.Math.Algebra.Linalg213.Permutation
  (swapAt swapAt_prefix psign inversions iota perms)
open E213.Lib.Math.Algebra.Linalg213.PermSign
  (psign_swapAt descent_of_inv_pos sorted_perm_eq_iota inv_prefix_swap swapAt_mem_perms
   inv_zero_imp_sorted)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (perm_length lt_of_mem_iota map_eq_of_mem length_iota)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (getD_iota)
open E213.Tactic.List213 (getD_ge length_append)

/-- The permutation matrix of a value-list: row `i` has a `1` in column `σ i`, else `0`. -/
def permMatrix (σ : List Nat) : Nat → Nat → Int :=
  fun i j => if σ.getD i 0 = j then 1 else 0

/-! ## §1 — `getD` at and around the swapped pair -/

/-- `(pre ++ a :: rest).getD pre.length 0 = a`. -/
theorem getD_at_len : ∀ (pre : List Nat) (a : Nat) (rest : List Nat),
    (pre ++ a :: rest).getD pre.length 0 = a
  | [],       a, rest => rfl
  | p :: pre, a, rest => getD_at_len pre a rest

/-- `(pre ++ a :: b :: rest).getD (pre.length + 1) 0 = b`. -/
theorem getD_at_len_succ : ∀ (pre : List Nat) (a b : Nat) (rest : List Nat),
    (pre ++ a :: b :: rest).getD (pre.length + 1) 0 = b
  | [],       a, b, rest => rfl
  | p :: pre, a, b, rest => getD_at_len_succ pre a b rest

/-- Off the two swapped positions, swapping the pair leaves `getD` unchanged. -/
theorem getD_swap_outside : ∀ (pre : List Nat) (y x : Nat) (l : List Nat) (i : Nat),
    i ≠ pre.length → i ≠ pre.length + 1 →
    (pre ++ x :: y :: l).getD i 0 = (pre ++ y :: x :: l).getD i 0
  | [],       y, x, l, i, h0, h1 => by
    cases i with
    | zero => exact absurd rfl h0
    | succ i' =>
      cases i' with
      | zero => exact absurd rfl h1
      | succ i'' => rfl
  | p :: pre, y, x, l, i, h0, h1 => by
    cases i with
    | zero => rfl
    | succ i' =>
      show (pre ++ x :: y :: l).getD i' 0 = (pre ++ y :: x :: l).getD i' 0
      exact getD_swap_outside pre y x l i'
        (fun h => h0 (congrArg (· + 1) h)) (fun h => h1 (congrArg (· + 1) h))

/-! ## §2 — an adjacent position-swap is a row swap of the permutation matrix -/

/-- ★ **`permMatrix (pre ++ x :: y :: l) = swapRows pre.length (pre.length+1) (permMatrix (pre ++
    y :: x :: l))`** (pointwise): swapping two adjacent entries of `σ` swaps the two corresponding
    rows of `permMatrix σ`. -/
theorem permMatrix_swap_pointwise (pre : List Nat) (y x : Nat) (l : List Nat) (i j : Nat) :
    permMatrix (pre ++ x :: y :: l) i j
      = swapRows pre.length (pre.length + 1) (permMatrix (pre ++ y :: x :: l)) i j := by
  by_cases h1 : i = pre.length
  · subst h1
    show (if (pre ++ x :: y :: l).getD pre.length 0 = j then (1 : Int) else 0)
       = (if pre.length = pre.length then permMatrix (pre ++ y :: x :: l) (pre.length + 1) j
          else if pre.length = pre.length + 1 then permMatrix (pre ++ y :: x :: l) pre.length j
          else permMatrix (pre ++ y :: x :: l) pre.length j)
    rw [if_pos rfl, getD_at_len pre x (y :: l)]
    show (if x = j then (1 : Int) else 0)
       = (if (pre ++ y :: x :: l).getD (pre.length + 1) 0 = j then (1 : Int) else 0)
    rw [getD_at_len_succ pre y x l]
  · by_cases h2 : i = pre.length + 1
    · subst h2
      show (if (pre ++ x :: y :: l).getD (pre.length + 1) 0 = j then (1 : Int) else 0)
         = (if pre.length + 1 = pre.length then permMatrix (pre ++ y :: x :: l) (pre.length + 1) j
            else if pre.length + 1 = pre.length + 1 then permMatrix (pre ++ y :: x :: l) pre.length j
            else permMatrix (pre ++ y :: x :: l) (pre.length + 1) j)
      rw [if_neg h1, if_pos rfl, getD_at_len_succ pre x y l]
      show (if y = j then (1 : Int) else 0)
         = (if (pre ++ y :: x :: l).getD pre.length 0 = j then (1 : Int) else 0)
      rw [getD_at_len pre y (x :: l)]
    · show (if (pre ++ x :: y :: l).getD i 0 = j then (1 : Int) else 0)
         = (if i = pre.length then permMatrix (pre ++ y :: x :: l) (pre.length + 1) j
            else if i = pre.length + 1 then permMatrix (pre ++ y :: x :: l) pre.length j
            else permMatrix (pre ++ y :: x :: l) i j)
      rw [if_neg h1, if_neg h2, getD_swap_outside pre y x l i h1 h2]
      rfl

/-! ## §3 — base: the identity-shaped matrix at `iota n` -/

/-- ★ **`det n (permMatrix (iota n)) = 1`** — `permMatrix (iota n)` is lower-triangular with a
    unit diagonal. -/
theorem det_permMatrix_iota (n : Nat) : det n (permMatrix (iota n)) = 1 := by
  rw [det_lower_triangular n (permMatrix (iota n)) (fun i j hij => by
        show (if (iota n).getD i 0 = j then (1 : Int) else 0) = 0
        have hne : (iota n).getD i 0 ≠ j := by
          rcases Nat.lt_or_ge i n with hin | hin
          · rw [getD_iota n i hin]; exact Nat.ne_of_lt hij
          · rw [getD_ge 0 (by rw [length_iota]; exact hin)]
            exact Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) hij)
        rw [if_neg hne])]
  rw [map_eq_of_mem (fun i => permMatrix (iota n) i i) (fun _ => (1 : Int)) (fun i hi => by
        show (if (iota n).getD i 0 = i then (1 : Int) else 0) = 1
        rw [getD_iota n i (lt_of_mem_iota hi), if_pos rfl]),
      prodZ_map_one]

/-! ## §4 — the bubble-sort reduction -/

/-- Fuel-bounded `det (permMatrix σ) = psign σ` (induction on `inversions σ ≤ fuel`). -/
theorem det_permMatrix_aux : ∀ (fuel n : Nat) (σ : List Nat), σ ∈ perms n →
    inversions σ ≤ fuel → det n (permMatrix σ) = psign σ
  | 0, n, σ, hσ, hf =>
    by
      have hz : inversions σ = 0 := Nat.le_antisymm hf (Nat.zero_le _)
      have hiota : σ = iota n := sorted_perm_eq_iota n σ (inv_zero_imp_sorted σ hz) hσ
      have hL : det n (permMatrix σ) = 1 := by rw [hiota]; exact det_permMatrix_iota n
      have hR : psign σ = 1 := by show E213.Lib.Math.Algebra.Linalg213.DetN.altSign (inversions σ) = 1; rw [hz]; rfl
      rw [hL, hR]
  | fuel + 1, n, σ, hσ, hf =>
    by
      by_cases hz : inversions σ = 0
      · have hiota : σ = iota n := sorted_perm_eq_iota n σ (inv_zero_imp_sorted σ hz) hσ
        have hL : det n (permMatrix σ) = 1 := by rw [hiota]; exact det_permMatrix_iota n
        have hR : psign σ = 1 := by show E213.Lib.Math.Algebra.Linalg213.DetN.altSign (inversions σ) = 1; rw [hz]; rfl
        rw [hL, hR]
      · obtain ⟨pre, y, x, l, he, hxy⟩ := descent_of_inv_pos σ hz
        subst he
        have hlen : (pre ++ y :: x :: l).length = n := perm_length hσ
        have hk1n : pre.length + 1 < n := by
          rw [← hlen, length_append pre (y :: x :: l)]
          exact Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.succ_pos l.length)) pre.length
        have hkn : pre.length < n := Nat.lt_of_succ_lt hk1n
        -- the swapped list S = pre ++ x :: y :: l ∈ perms n with one fewer inversion
        have hSperm : (pre ++ x :: y :: l) ∈ perms n := by
          have hm := swapAt_mem_perms n pre.length (pre ++ y :: x :: l) hσ
          rwa [swapAt_prefix pre y x l] at hm
        have hSf : inversions (pre ++ x :: y :: l) ≤ fuel := by
          have hf' := hf
          rw [inv_prefix_swap pre y x l hxy] at hf'
          exact Nat.le_of_succ_le_succ hf'
        -- det of S = − det of O (row swap)
        have hdetS : det n (permMatrix (pre ++ x :: y :: l))
            = - det n (permMatrix (pre ++ y :: x :: l)) := by
          rw [det_congr n (permMatrix_swap_pointwise pre y x l)]
          exact det_swapRows n pre.length (pre.length + 1)
            (Nat.ne_of_lt (Nat.lt_succ_self pre.length)) hkn hk1n (permMatrix (pre ++ y :: x :: l))
        -- recursion + sign flip
        have hrec : det n (permMatrix (pre ++ x :: y :: l)) = psign (pre ++ x :: y :: l) :=
          det_permMatrix_aux fuel n (pre ++ x :: y :: l) hSperm hSf
        have hps : psign (pre ++ x :: y :: l) = - psign (pre ++ y :: x :: l) := by
          have h := psign_swapAt pre y x l (Ne.symm (Nat.ne_of_lt hxy))
          rwa [swapAt_prefix pre y x l] at h
        rw [show det n (permMatrix (pre ++ y :: x :: l))
              = - det n (permMatrix (pre ++ x :: y :: l)) from by rw [hdetS, Int.neg_neg],
            hrec, hps, Int.neg_neg]

/-- ★★★ **The determinant of a permutation matrix is the permutation's sign.**
    `det n (permMatrix σ) = psign σ` for any `σ ∈ perms n` — the two readings of a permutation
    (matrix vs. sign) coincide. -/
theorem det_permMatrix (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) :
    det n (permMatrix σ) = psign σ :=
  det_permMatrix_aux (inversions σ) n σ hσ (Nat.le_refl _)

end E213.Lib.Math.Algebra.Linalg213.PermMatrixDet
