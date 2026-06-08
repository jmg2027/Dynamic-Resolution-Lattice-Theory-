import E213.Lib.Math.Algebra.Linalg213.Permutation

/-!
# Linalg213 — the cyclic-shift permutation and its sign `altSign(k−1)`

The companion (cyclic-shift) matrix of an order-`k` recurrence has determinant sign
`altSign(k−1)` (`Cauchy.CasoratianDeterminant.det_companion`).  This file identifies that
sign as the **permutation sign** of the underlying `k`-cycle, putting the Casoratian
multiplier on the same inversion-sign readout as `det(permMatrix)` / Legendre / Zolotarev
(the "permutation under three readouts" — this is the fourth reading).

The `(m+1)`-cycle `(0 1 … m)` in one-line notation is `[1, 2, …, m, 0]` (`cycShift m`):
each of `1…m` precedes the trailing `0`, contributing exactly one inversion each, so

  `inversions (cycShift m) = m`,   `psign (cycShift m) = altSign m`.

`cycShift m` is certified a genuine permutation of `[0,…,m]` (`cycShift_perm_iota`).

All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.CyclicShiftSign

open E213.Lib.Math.Algebra.Linalg213.Permutation
  (ltCount inversions psign LPerm iota ltCount_append)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign)

/-! ## §1 — the ascending run `upFrom s n = [s, s+1, …, s+n−1]` -/

/-- `[s, s+1, …, s+n−1]` (the ascending block). -/
def upFrom (s : Nat) : Nat → List Nat
  | 0     => []
  | n + 1 => s :: upFrom (s + 1) n

/-- The ascending block grows at the **end** as well: `upFrom s (n+1) = upFrom s n ++ [s+n]`. -/
theorem upFrom_snoc : ∀ (n s : Nat), upFrom s (n + 1) = upFrom s n ++ [s + n]
  | 0,     s => rfl
  | n + 1, s => by
      show s :: upFrom (s + 1) (n + 1) = s :: (upFrom (s + 1) n ++ [s + (n + 1)])
      have he : s + 1 + n = s + (n + 1) := by
        show Nat.succ s + n = s + Nat.succ n
        rw [Nat.succ_add, Nat.add_succ]
      rw [upFrom_snoc n (s + 1), he]

/-- An element strictly below the whole ascending block contributes no inversion against it:
    `a ≤ s ⟹ ltCount a (upFrom s n) = 0`. -/
theorem ltCount_upFrom_zero : ∀ (n s a : Nat), a ≤ s → ltCount a (upFrom s n) = 0
  | 0,     _, _, _   => rfl
  | n + 1, s, a, hle => by
      show (if s < a then 1 else 0) + ltCount a (upFrom (s + 1) n) = 0
      rw [if_neg (fun (h : s < a) => Nat.lt_irrefl s (Nat.lt_of_lt_of_le h hle)),
          ltCount_upFrom_zero n (s + 1) a (Nat.le_trans hle (Nat.le_succ s))]

/-! ## §2 — `inversions (upFrom s n ++ [0]) = n` -/

/-- ★★★ Appending a `0` after an ascending block of positives adds exactly one inversion per
    element: `0 < s ⟹ inversions (upFrom s n ++ [0]) = n`.  The trailing `0` is below all
    `n` entries, and the block itself is inversion-free. -/
theorem inversions_upFrom_append_zero :
    ∀ (n s : Nat), 0 < s → inversions (upFrom s n ++ [0]) = n
  | 0,     _, _  => rfl
  | n + 1, s, hs => by
      show ltCount s (upFrom (s + 1) n ++ [0]) + inversions (upFrom (s + 1) n ++ [0]) = n + 1
      rw [ltCount_append s (upFrom (s + 1) n) [0],
          ltCount_upFrom_zero n (s + 1) s (Nat.le_succ s),
          inversions_upFrom_append_zero n (s + 1) (Nat.succ_pos s)]
      have hl0 : ltCount s [0] = 1 := by
        show (if (0 : Nat) < s then 1 else 0) + 0 = 1
        rw [if_pos hs]
      rw [hl0, Nat.zero_add, Nat.add_comm 1 n]

/-! ## §3 — the cyclic shift `[1,…,m,0]`, its inversions, sign, and permutation-ness -/

/-- The one-line notation of the `(m+1)`-cycle `(0 1 … m)`: `[1, 2, …, m, 0]`. -/
def cycShift (m : Nat) : List Nat := upFrom 1 m ++ [0]

/-- ★★★ **`inversions (cycShift m) = m`.**  The trailing `0` sits below all of `1…m`. -/
theorem cycShift_inversions (m : Nat) : inversions (cycShift m) = m :=
  inversions_upFrom_append_zero m 1 Nat.one_pos

/-- ★★★★ **`psign (cycShift m) = altSign m`.**  The `(m+1)`-cycle's sign is `(−1)^m` —
    exactly the companion-determinant sign `altSign m = altSign((m+1)−1)`. -/
theorem cycShift_psign (m : Nat) : psign (cycShift m) = altSign m := by
  show altSign (inversions (cycShift m)) = altSign m
  rw [cycShift_inversions m]

/-- Moving the last entry to the front is a list-permutation (a rotation). -/
theorem rotate_lperm {α : Type} : ∀ (L : List α) (x : α), LPerm (L ++ [x]) (x :: L)
  | [],      x => LPerm.cons x LPerm.nil
  | a :: L', x => LPerm.trans (LPerm.cons a (rotate_lperm L' x)) (LPerm.swap x a L')

/-- `iota (n+1) = [0,1,…,n] = 0 :: upFrom 1 n`. -/
theorem iota_succ_eq : ∀ n, iota (n + 1) = 0 :: upFrom 1 n
  | 0     => rfl
  | n + 1 => by
      show iota (n + 1) ++ [n + 1] = 0 :: upFrom 1 (n + 1)
      rw [iota_succ_eq n]
      show 0 :: (upFrom 1 n ++ [n + 1]) = 0 :: upFrom 1 (n + 1)
      rw [upFrom_snoc n 1, Nat.add_comm 1 n]

/-- ★★★ **`cycShift m` is a genuine permutation of `[0,…,m]`.**  So `psign (cycShift m)` is the
    sign of an actual permutation, not of an arbitrary list — the cyclic shift `(0 1 … m)`. -/
theorem cycShift_perm_iota (m : Nat) : LPerm (cycShift m) (iota (m + 1)) := by
  show LPerm (upFrom 1 m ++ [0]) (iota (m + 1))
  rw [iota_succ_eq m]
  exact rotate_lperm (upFrom 1 m) 0

end E213.Lib.Math.Algebra.Linalg213.CyclicShiftSign
