import E213.Lib.Math.NumberTheory.ModArith.Zolotarev
import E213.Lib.Math.NumberTheory.ModArith.ZolotarevConverse
import E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot

/-!
# ZolotarevCycle — the odd-cycle witness (brick 7), completing the full Zolotarev identity

A primitive root `g` has `psign (mulPerm g p) = −1`.  This is the single input that
`ZolotarevConverse.zolotarev_iff` needs: with it, `psign (mulPerm a p) = 1 ⟺ a` is a QR for **all**
units `a`.

`mulPerm g` (`v ↦ g·v mod p`) fixes `0` and is a single `(p−1)`-cycle on the units.  It is conjugate
to the **standard rotation** `S = [0, p−1, 1, 2, …, p−2]` (`S(0)=0`, `S(1)=p−1`, `S(i)=i−1` for
`2 ≤ i`) by the discrete-log list `τ(i) = g^(p−1−i) mod p` (`τ(0)=0`):
`composeList (mulPerm g) τ = composeList τ S` (both send `i ↦ g^(p−i)`-shaped values), so
`psign (mulPerm g)·psign τ = psign τ·psign S`, hence `psign (mulPerm g) = psign S` (a `±1` cancels).
`S` has exactly `p−2` inversions (`p−1` against the trailing block, the ascending tail sorted), so
`psign S = (−1)^(p−2) = −1` (`p` odd).

  * `asc` — the ascending block `[lo, lo+1, …, lo+n−1]`, with `inversions = 0`.
  * `S` / `cycS` — the standard rotation; `inversions_cycS = p−2`; ★★ `psign_cycS = −1`.

This file builds the inversion-count payoff (`psign S = −1`); the conjugation and final assembly
are `psign_mulPerm_primitive` / `zolotarev_full`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota perms psign inversions ltCount)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (lt_of_mem_iota length_iota nodup_iota)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList getD_iota)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul altSign_self)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add)
open E213.Lib.Math.Algebra.Linalg213.DetMul (funcs nodup_imp_perm mem_tuples)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose (nodup_map_restrict)
open E213.Lib.Math.Algebra.Linalg213.Laplace (mem_iota_of_lt)
open E213.Tactic.List213 (getD_ge getD_map_ib list_ext_getD exists_of_mem_map)
open E213.Lib.Math.NumberTheory.ModArith.Zolotarev (mulPerm length_map_pure)
open E213.Tactic.NatHelper (add_sub_of_le sub_add_cancel add_sub_cancel_right)

/-! ## §1 — the ascending block and its inversion count -/

/-- The ascending block `[lo, lo+1, …, lo+n−1]`. -/
def asc (lo : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => lo :: asc (lo + 1) k

theorem asc_length (lo n : Nat) : (asc lo n).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ k ih => show (lo :: asc (lo + 1) k).length = k + 1; rw [List.length_cons, ih]

theorem asc_getD (lo n i : Nat) (hi : i < n) : (asc lo n).getD i 0 = lo + i := by
  induction n generalizing lo i with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    cases i with
    | zero => show (lo :: asc (lo + 1) k).getD 0 0 = lo + 0; rw [Nat.add_zero]; rfl
    | succ j =>
      show (lo :: asc (lo + 1) k).getD (j + 1) 0 = lo + (j + 1)
      rw [show (lo :: asc (lo + 1) k).getD (j + 1) 0 = (asc (lo + 1) k).getD j 0 from rfl,
          ih (lo + 1) j (Nat.lt_of_succ_lt_succ hi)]
      rw [Nat.add_assoc, Nat.add_comm 1 j]

/-- Nothing is `< 0`. -/
theorem ltCount_zero : ∀ L : List Nat, ltCount 0 L = 0
  | [] => rfl
  | y :: ys => by
    show (if y < 0 then 1 else 0) + ltCount 0 ys = 0
    rw [if_neg (Nat.not_lt_zero y), Nat.zero_add, ltCount_zero ys]

/-- If the threshold `c` is `≤ lo`, no element of `asc lo n` is `< c`. -/
theorem ltCount_asc_ge (c : Nat) : ∀ (n lo : Nat), c ≤ lo → ltCount c (asc lo n) = 0
  | 0, _, _ => rfl
  | k + 1, lo, h => by
    show (if lo < c then 1 else 0) + ltCount c (asc (lo + 1) k) = 0
    rw [if_neg (Nat.not_lt.mpr h), Nat.zero_add,
        ltCount_asc_ge c k (lo + 1) (Nat.le_trans h (Nat.le_succ lo))]

/-- If every element of `asc lo n` is `< c` (i.e. `lo + n ≤ c`), all `n` are counted. -/
theorem ltCount_asc_all (c : Nat) : ∀ (n lo : Nat), lo + n ≤ c → ltCount c (asc lo n) = n
  | 0, _, _ => rfl
  | k + 1, lo, h => by
    show (if lo < c then 1 else 0) + ltCount c (asc (lo + 1) k) = k + 1
    have hlo : lo < c := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos k)) h
    rw [if_pos hlo, ltCount_asc_all c k (lo + 1)
        (by rw [Nat.add_assoc, Nat.add_comm 1 k]; exact h)]
    rw [Nat.add_comm]

/-- An ascending block has no inversions. -/
theorem inversions_asc : ∀ (n lo : Nat), inversions (asc lo n) = 0
  | 0, _ => rfl
  | k + 1, lo => by
    show ltCount lo (asc (lo + 1) k) + inversions (asc (lo + 1) k) = 0
    rw [ltCount_asc_ge lo k (lo + 1) (Nat.le_succ lo), inversions_asc k (lo + 1)]

/-! ## §2 — the standard rotation `S = [0, p−1, 1, 2, …, p−2]` -/

/-- The value of the standard rotation at index `i`: `0 ↦ 0`, `1 ↦ p−1`, `i ↦ i−1` (`i ≥ 2`). -/
def sFun (p i : Nat) : Nat := if i = 0 then 0 else if i = 1 then p - 1 else i - 1

/-- The standard rotation as a value list over `iota p`. -/
def cycS (p : Nat) : List Nat := (iota p).map (sFun p)

theorem cycS_length (p : Nat) : (cycS p).length = p := by
  show ((iota p).map (sFun p)).length = p; rw [length_map_pure, length_iota]

theorem cycS_getD (p i : Nat) (hi : i < p) : (cycS p).getD i 0 = sFun p i := by
  show ((iota p).map (sFun p)).getD i 0 = sFun p i
  rw [getD_map_ib (sFun p) 0 0 (iota p) i (by rw [length_iota]; exact hi), getD_iota p i hi]

/-- The explicit form of `S`: `0 :: (p−1) :: asc 1 (p−2)`. -/
theorem cycS_explicit (p : Nat) (hp : 2 ≤ p) :
    cycS p = 0 :: (p - 1) :: asc 1 (p - 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le hp).symm⟩
  apply list_ext_getD 0
  · rw [cycS_length]
    show e + 2 = (0 :: (e + 2 - 1) :: asc 1 (e + 2 - 2)).length
    rw [List.length_cons, List.length_cons, asc_length, add_sub_cancel_right e 2]
  · intro i
    rcases Nat.lt_or_ge i (e + 2) with hi | hi
    · rw [cycS_getD (e + 2) i hi]
      cases i with
      | zero => rfl
      | succ j =>
        cases j with
        | zero => rfl
        | succ k =>
          show sFun (e + 2) (k + 2) = (asc 1 (e + 2 - 2)).getD k 0
          rw [add_sub_cancel_right e 2]
          have hk : k < e := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)
          rw [asc_getD 1 e k hk]
          show k + 1 = 1 + k
          exact Nat.add_comm k 1
    · rw [getD_ge 0 (by rw [cycS_length]; exact hi),
          getD_ge 0 (by
            show (0 :: (e + 2 - 1) :: asc 1 (e + 2 - 2)).length ≤ i
            rw [List.length_cons, List.length_cons, asc_length, add_sub_cancel_right e 2]
            exact hi)]

/-- The inversion count of the standard rotation is `p − 2`. -/
theorem inversions_cycS (p : Nat) (hp : 2 ≤ p) : inversions (cycS p) = p - 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le hp).symm⟩
  rw [cycS_explicit (e + 2) hp, add_sub_cancel_right e 2]
  show ltCount 0 ((e + 2 - 1) :: asc 1 e) + inversions ((e + 2 - 1) :: asc 1 e) = e
  rw [ltCount_zero, Nat.zero_add]
  show ltCount (e + 2 - 1) (asc 1 e) + inversions (asc 1 e) = e
  rw [inversions_asc e 1, Nat.add_zero]
  exact ltCount_asc_all (e + 2 - 1) e 1 (Nat.le_of_eq (Nat.add_comm 1 e))

/-! ## §3 — the sign of the standard rotation is `−1` (for odd `p`) -/

/-- `altSign (2k + 1) = −1`. -/
theorem altSign_odd (k : Nat) : altSign (2 * k + 1) = -1 := by
  have h2k : altSign (2 * k) = 1 := by
    rw [show 2 * k = k + k from by rw [Nat.two_mul], altSign_add k k, altSign_self k]
  rw [show 2 * k + 1 = (2 * k) + 1 from rfl, altSign_add (2 * k) 1, h2k]
  show (1 : Int) * altSign 1 = -1
  rw [Int.one_mul]; rfl

/-- ★★ **The standard rotation is odd**: `psign (cycS p) = −1` for an odd prime-sized `p`
    (`2m = p − 1`, `m ≥ 1`).  Its `p − 2 = 2(m−1) + 1` inversions are odd. -/
theorem psign_cycS (p m : Nat) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hp : 2 ≤ p) :
    psign (cycS p) = -1 := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le hp).symm⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (sub_add_cancel hm1).symm⟩
  show altSign (inversions (cycS (e + 2))) = -1
  rw [inversions_cycS (e + 2) hp, add_sub_cancel_right e 2]
  rw [Nat.mul_succ] at h2m
  -- h2m : 2 * m' + 2 = e + 2 - 1  (defeq Nat.succ (2*m'+1) = Nat.succ e)
  have he : 2 * m' + 1 = e := Nat.succ.inj h2m
  rw [← he]
  exact altSign_odd m'

end E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle
