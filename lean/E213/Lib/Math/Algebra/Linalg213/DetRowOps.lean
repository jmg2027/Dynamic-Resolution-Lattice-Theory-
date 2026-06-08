import E213.Lib.Math.Algebra.Linalg213.DetTriangular

/-!
# Linalg213 — elementary row operations on the determinant

The workhorse of determinant computation (Gaussian elimination): **adding a multiple of one row
to another leaves the determinant unchanged**.  No new permutation/sign theory — it falls out of
the two properties already in hand:

  · row-multilinearity (`det_setRow_add` / `det_setRow_smul`, `Laplace`), and
  · the alternating property's degeneracy form (`det_rows_eq_ne` — two equal rows ⟹ `det = 0`).

`det (rowᵢ += t·rowⱼ) = det(rowᵢ unchanged) + t·det(rowᵢ ← rowⱼ) = det M + t·0 = det M`.

A **row swap** is not elementary, but factors into the above: three adds land `(rowᵢ,rowⱼ)` at
`(rowⱼ,−rowᵢ)`, then negating `rowⱼ` (scale by `−1`) gives `(rowⱼ,rowᵢ)` — so *any* row swap
negates `det` (`det_swapRows`), generalizing the adjacent `Laplace.det_rowSwap`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.DetRowOps

open E213.Lib.Math.Algebra.Linalg213.DetN (det det_congr)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (setRow setRow_at setRow_off)
open E213.Lib.Math.Algebra.Linalg213.Laplace (det_setRow_add det_setRow_smul det_rows_eq_ne)
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton (add_zero' mul_zero' one_mul')

/-- Add `t ·` row `j` to row `i`: `rowᵢ ← rowᵢ + t·rowⱼ`. -/
def addRowMul (i j : Nat) (t : Int) (M : Nat → Nat → Int) : Nat → Nat → Int :=
  setRow i (fun c => M i c + t * M j c) M

/-- Setting row `i` to its own value is the identity. -/
theorem setRow_self (i : Nat) (M : Nat → Nat → Int) (a c : Nat) :
    setRow i (fun c => M i c) M a c = M a c := by
  show (if a = i then M i c else M a c) = M a c
  by_cases h : a = i
  · rw [if_pos h, h]
  · rw [if_neg h]

/-- ★★ **Adding a multiple of row `j` to a distinct row `i` leaves `det` unchanged.**
    The elementary row operation behind Gaussian elimination — `det` is invariant under
    `rowᵢ ← rowᵢ + t·rowⱼ` (`i ≠ j`). -/
theorem det_addRowMul (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n) (t : Int)
    (M : Nat → Nat → Int) : det n (addRowMul i j t M) = det n M := by
  show det n (setRow i (fun c => M i c + t * M j c) M) = det n M
  rw [det_setRow_add n i hi (fun c => M i c) (fun c => t * M j c) M,
      det_congr n (setRow_self i M),
      det_setRow_smul n i hi t (fun c => M j c) M,
      det_rows_eq_ne (setRow i (fun c => M j c) M) n i j hij hi hj (fun c => by
        rw [setRow_at i (fun c => M j c) M, setRow_off i (fun c => M j c) M (Ne.symm hij)])]
  show det n M + t * 0 = det n M
  rw [mul_zero', add_zero']

/-- ★ **Adding row `j` to a distinct row `i` (the `t = 1` case) leaves `det` unchanged.** -/
theorem det_addRow (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n) (M : Nat → Nat → Int) :
    det n (setRow i (fun c => M i c + M j c) M) = det n M := by
  have heq : ∀ a c, setRow i (fun c => M i c + M j c) M a c = addRowMul i j 1 M a c := by
    intro a c
    show (if a = i then M i c + M j c else M a c)
       = (if a = i then M i c + 1 * M j c else M a c)
    by_cases h : a = i
    · rw [if_pos h, if_pos h, one_mul']
    · rw [if_neg h, if_neg h]
  rw [det_congr n heq, det_addRowMul n i j hij hi hj 1 M]

/-! ## Row swap negates the determinant (via three additions + one negation)

A row swap is *not* an elementary operation, but it factors into ones that are: from `(rowᵢ, rowⱼ)`,
`rowᵢ += rowⱼ`, `rowⱼ −= rowᵢ`, `rowᵢ += rowⱼ` lands at `(rowⱼ, −rowᵢ)` (three `det`-preserving
adds), and negating `rowⱼ` gives `(rowⱼ, rowᵢ)` — multiplying `det` by `−1`.  So an **arbitrary**
row swap negates the determinant, not just an adjacent one (`Laplace.det_rowSwap`).  No new
permutation/sign theory. -/

/-- `addRowMul` at the modified row `i`. -/
theorem addRowMul_at (i j : Nat) (t : Int) (M : Nat → Nat → Int) (c : Nat) :
    addRowMul i j t M i c = M i c + t * M j c := setRow_at i _ M c

/-- `addRowMul` off the modified row. -/
theorem addRowMul_off (i j : Nat) (t : Int) (M : Nat → Nat → Int) {a : Nat} (h : a ≠ i) (c : Nat) :
    addRowMul i j t M a c = M a c := setRow_off i _ M h c

/-- Swap rows `i` and `j`. -/
def swapRows (i j : Nat) (M : Nat → Nat → Int) : Nat → Nat → Int :=
  fun a c => if a = i then M j c else if a = j then M i c else M a c

theorem swapRows_i (i j : Nat) (M : Nat → Nat → Int) (c : Nat) : swapRows i j M i c = M j c :=
  if_pos rfl

theorem swapRows_j (i j : Nat) (hij : i ≠ j) (M : Nat → Nat → Int) (c : Nat) :
    swapRows i j M j c = M i c := by
  show (if j = i then M j c else if j = j then M i c else M j c) = M i c
  rw [if_neg (Ne.symm hij), if_pos rfl]

theorem swapRows_other (i j : Nat) (M : Nat → Nat → Int) {a : Nat} (hai : a ≠ i) (haj : a ≠ j)
    (c : Nat) : swapRows i j M a c = M a c := by
  show (if a = i then M j c else if a = j then M i c else M a c) = M a c
  rw [if_neg hai, if_neg haj]

/-- ★★ **An arbitrary row swap negates the determinant** (`i ≠ j`).  The alternating property for
    *any* pair of rows — `det_rowSwap` (`Laplace`) gives only the adjacent case.  A swap factors as
    three `det`-preserving adds (`rowᵢ += rowⱼ`, `rowⱼ −= rowᵢ`, `rowᵢ += rowⱼ` lands at
    `(rowⱼ, −rowᵢ)`) followed by negating `rowⱼ` (scales `det` by `−1`). -/
theorem det_swapRows (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n) (M : Nat → Nat → Int) :
    det n (swapRows i j M) = - det n M := by
  have e1 : det n (addRowMul i j 1 M) = det n M := det_addRowMul n i j hij hi hj 1 M
  have e2 : det n (addRowMul j i (-1) (addRowMul i j 1 M)) = det n M := by
    rw [det_addRowMul n j i (Ne.symm hij) hj hi (-1) (addRowMul i j 1 M), e1]
  have e3 : det n (addRowMul i j 1 (addRowMul j i (-1) (addRowMul i j 1 M))) = det n M := by
    rw [det_addRowMul n i j hij hi hj 1 (addRowMul j i (-1) (addRowMul i j 1 M)), e2]
  -- the swapped matrix = negate row `j` of the triple-add matrix
  have key : ∀ a c, swapRows i j M a c
      = setRow j (fun c => (-1) * (addRowMul i j 1 (addRowMul j i (-1) (addRowMul i j 1 M))) j c)
          (addRowMul i j 1 (addRowMul j i (-1) (addRowMul i j 1 M))) a c := by
    intro a c
    by_cases hai : a = i
    · rw [hai, swapRows_i, setRow_off j _ _ hij,
          addRowMul_at i j 1 (addRowMul j i (-1) (addRowMul i j 1 M)) c,
          addRowMul_off j i (-1) (addRowMul i j 1 M) hij c,
          addRowMul_at j i (-1) (addRowMul i j 1 M) c,
          addRowMul_at i j 1 M c, addRowMul_off i j 1 M (Ne.symm hij) c]
      ring_intZ
    · by_cases haj : a = j
      · rw [haj, swapRows_j i j hij, setRow_at,
            addRowMul_off i j 1 (addRowMul j i (-1) (addRowMul i j 1 M)) (Ne.symm hij) c,
            addRowMul_at j i (-1) (addRowMul i j 1 M) c,
            addRowMul_off i j 1 M (Ne.symm hij) c, addRowMul_at i j 1 M c]
        ring_intZ
      · rw [swapRows_other i j M hai haj, setRow_off j _ _ haj,
            addRowMul_off i j 1 (addRowMul j i (-1) (addRowMul i j 1 M)) hai c,
            addRowMul_off j i (-1) (addRowMul i j 1 M) haj c,
            addRowMul_off i j 1 M hai c]
  rw [det_congr n key,
      det_setRow_smul n j hj (-1)
        (fun c => (addRowMul i j 1 (addRowMul j i (-1) (addRowMul i j 1 M))) j c)
        (addRowMul i j 1 (addRowMul j i (-1) (addRowMul i j 1 M))),
      det_congr n (setRow_self j (addRowMul i j 1 (addRowMul j i (-1) (addRowMul i j 1 M)))), e3]
  show (-1 : Int) * det n M = - det n M
  ring_intZ

end E213.Lib.Math.Algebra.Linalg213.DetRowOps
