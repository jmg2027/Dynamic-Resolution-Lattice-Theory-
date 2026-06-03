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

open E213.Lib.Math.Linalg213.DetN (colShift minor altSign altSign_add)
open E213.Lib.Math.Linalg213.Permutation
  (prodDiagFrom psign leibTerm leibDet perms sumZ ltCount inversions psign_cons)
open E213.Lib.Math.Linalg213.PermClosure (cnt)

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

/-! ## §2 — the per-term factorization

For `rel ∈ perms n`, the permutation `j :: rel.map (colShift j)` of `[0,…,n]` has
`leibTerm M (j :: rel.map (colShift j)) = altSign j · M 0 j · leibTerm (minor M j) rel`:
the diagonal product gives the minor's (B′), the sign splits via `psign_cons` with the leading
`ltCount = j` (C′) and `psign` preserved under the order-embedding `colShift j` (A′). -/

/-- **B′** — the diagonal product of `M` over the `colShift`-image equals the minor's. -/
theorem prodDiag_minor (M : Nat → Nat → Int) (j : Nat) :
    ∀ (i : Nat) (rel : List Nat),
      prodDiagFrom M (i + 1) (rel.map (colShift j)) = prodDiagFrom (minor M j) i rel
  | _, []      => rfl
  | i, l :: ls => by
    show minor M j i l * prodDiagFrom M (i + 1 + 1) (ls.map (colShift j))
       = minor M j i l * prodDiagFrom (minor M j) (i + 1) ls
    rw [prodDiag_minor M j (i + 1) ls]

/-- `colShift j` is strictly monotone. -/
theorem colShift_lt_mono (j b a : Nat) (h : b < a) : colShift j b < colShift j a := by
  show (if b < j then b else b + 1) < (if a < j then a else a + 1)
  by_cases hb : b < j
  · by_cases ha : a < j
    · rw [if_pos hb, if_pos ha]; exact h
    · rw [if_pos hb, if_neg ha]; exact Nat.lt_succ_of_lt h
  · by_cases ha : a < j
    · exact absurd (Nat.lt_trans h ha) hb
    · rw [if_neg hb, if_neg ha]; exact Nat.succ_lt_succ h

/-- `colShift j` is monotone. -/
theorem colShift_le_mono (j a b : Nat) (h : a ≤ b) : colShift j a ≤ colShift j b := by
  show (if a < j then a else a + 1) ≤ (if b < j then b else b + 1)
  by_cases ha : a < j
  · by_cases hb : b < j
    · rw [if_pos ha, if_pos hb]; exact h
    · rw [if_pos ha, if_neg hb]; exact Nat.le_succ_of_le h
  · have hb : ¬ b < j := fun hbj => ha (Nat.lt_of_le_of_lt h hbj)
    rw [if_neg ha, if_neg hb]; exact Nat.succ_le_succ h

/-- **A′ (count)** — `ltCount` is preserved under the order-embedding `colShift j`. -/
theorem ltCount_map_colShift (j a : Nat) : ∀ (rel : List Nat),
    ltCount (colShift j a) (rel.map (colShift j)) = ltCount a rel
  | []      => rfl
  | b :: bs => by
    show (if colShift j b < colShift j a then 1 else 0) + ltCount (colShift j a) (bs.map (colShift j))
       = (if b < a then 1 else 0) + ltCount a bs
    rw [ltCount_map_colShift j a bs]
    by_cases h : b < a
    · rw [if_pos h, if_pos (colShift_lt_mono j b a h)]
    · rw [if_neg h, if_neg (Nat.not_lt.mpr (colShift_le_mono j a b (Nat.not_lt.mp h)))]

/-- **A′ (inversions)** — `inversions` is preserved under `colShift j`. -/
theorem inversions_map_colShift (j : Nat) : ∀ (rel : List Nat),
    inversions (rel.map (colShift j)) = inversions rel
  | []      => rfl
  | a :: as => by
    show ltCount (colShift j a) (as.map (colShift j)) + inversions (as.map (colShift j))
       = ltCount a as + inversions as
    rw [ltCount_map_colShift j a as, inversions_map_colShift j as]

/-- **A′** — `psign` is preserved under `colShift j`. -/
theorem psign_map_colShift (j : Nat) (rel : List Nat) :
    psign (rel.map (colShift j)) = psign rel := by
  show altSign (inversions (rel.map (colShift j))) = altSign (inversions rel)
  rw [inversions_map_colShift]

end E213.Lib.Math.Linalg213.Laplace
