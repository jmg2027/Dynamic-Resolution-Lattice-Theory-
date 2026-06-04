import E213.Lib.Math.Linalg213.DetN
import E213.Lib.Math.Linalg213.PermClosure

/-!
# Linalg213 — the cofactor (Laplace) expansion of the Leibniz determinant

Toward integer **Cayley–Hamilton** (and the C-finite Hadamard product): expand `leibDet (n+1)`
along the first row.  The permutation value-lists of `[0,…,n]` whose **first** entry is `j`
biject with the permutations of the `(0,j)`-**minor**'s columns, via the column **relabeling**
`unshift j` (drop the value `j`, pulling larger values down) — the inverse of `DetN.colShift j`
(insert a gap at `j`).  The sign factor `(−1)ʲ` falls out of `PermClosure.psign_cons`
(`psign (j :: rest) = altSign (ltCount j rest) · psign rest`, and `ltCount j rest = j` for a
permutation `rest` of `[0,…,n] ∖ {j}`).

This file builds the relabeling foundation first.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.Laplace

open E213.Lib.Math.Linalg213.DetN (colShift)

/-! ## §1 — the minor relabeling (`unshift`, inverse of `colShift`) -/

/-- Drop the value `j`: values below `j` stay, values above shift down by one.  The inverse of
    `colShift j` (which inserts a gap at `j`) on `[0,…,n] ∖ {j}`. -/
def unshift (j v : Nat) : Nat := if v < j then v else v - 1

/-- ★ `colShift j ∘ unshift j = id` away from `j` — relabeling then re-inserting the gap. -/
theorem colShift_unshift {j v : Nat} (h : v ≠ j) : colShift j (unshift j v) = v := by
  show colShift j (if v < j then v else v - 1) = v
  by_cases hv : v < j
  · rw [if_pos hv]; show (if v < j then v else v + 1) = v; rw [if_pos hv]
  · rw [if_neg hv]
    have hjv : j < v := Nat.lt_of_le_of_ne (Nat.not_lt.mp hv) (fun e => h e.symm)
    obtain ⟨k, hk⟩ := Nat.le.dest hjv
    have hv1 : v - 1 = j + k := by rw [← hk, Nat.add_right_comm j 1 k]; exact Nat.succ_sub_one _
    rw [hv1]
    show (if j + k < j then j + k else (j + k) + 1) = v
    rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right j k)), ← hk, Nat.add_right_comm j 1 k]

/-- ★ `unshift j ∘ colShift j = id` — re-inserting the gap then relabeling. -/
theorem unshift_colShift (j l : Nat) : unshift j (colShift j l) = l := by
  show unshift j (if l < j then l else l + 1) = l
  by_cases hl : l < j
  · rw [if_pos hl]; show (if l < j then l else l - 1) = l; rw [if_pos hl]
  · rw [if_neg hl]
    show (if l + 1 < j then l + 1 else (l + 1) - 1) = l
    rw [if_neg (fun hlt => hl (Nat.lt_of_succ_lt hlt)), Nat.succ_sub_one]

/-- `colShift j v ≠ j` — the inserted gap is never `j`. -/
theorem colShift_ne (j l : Nat) : colShift j l ≠ j := by
  show (if l < j then l else l + 1) ≠ j
  by_cases hl : l < j
  · rw [if_pos hl]; exact Nat.ne_of_lt hl
  · rw [if_neg hl]
    exact fun e => hl (e ▸ Nat.lt_succ_self l)

end E213.Lib.Math.Linalg213.Laplace
