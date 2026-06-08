import E213.Lib.Math.Algebra.Linalg213.DetTriangular

/-!
# Linalg213 — elementary row operations on the determinant

The workhorse of determinant computation (Gaussian elimination): **adding a multiple of one row
to another leaves the determinant unchanged**.  No new permutation/sign theory — it falls out of
the two properties already in hand:

  · row-multilinearity (`det_setRow_add` / `det_setRow_smul`, `Laplace`), and
  · the alternating property's degeneracy form (`det_rows_eq_ne` — two equal rows ⟹ `det = 0`).

`det (rowᵢ += t·rowⱼ) = det(rowᵢ unchanged) + t·det(rowᵢ ← rowⱼ) = det M + t·0 = det M`.
All ∅-axiom.
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

end E213.Lib.Math.Algebra.Linalg213.DetRowOps
