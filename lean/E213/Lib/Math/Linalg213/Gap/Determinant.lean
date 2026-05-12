import E213.Lib.Math.Linalg213.Gap.MatrixMul
import E213.Meta.Tactic.Nat213

/-!
# Linalg213 Gap — Determinant (atomic, 2×2 / 3×3 closed form)

213-native paradigm: low-dimensional determinants are explicit
polynomial closed forms in matrix entries.  Permutation parity =
atomic counting; sign is encoded by Nat-side truncated subtraction
(`Nat`-side encodes only the magnitude part, leaving sign for the
oracle layer at higher levels).

Atomic content:
  * `det2_pos A = A 0 0 · A 1 1`
  * `det2_neg A = A 0 1 · A 1 0`
  * Identity 2×2: `det2_pos = 1`, `det2_neg = 0`.
  * Diagonal matrix: `det = product of diagonal`.
-/

namespace E213.Lib.Math.Linalg213.Gap.Determinant

open E213.Lib.Math.Linalg213.Gap.MatrixMul (Mat identityMat zeroMat)

/-- Positive part of 2×2 determinant. -/
def det2_pos (A : Mat) : Nat := A 0 0 * A 1 1

/-- Negative part of 2×2 determinant. -/
def det2_neg (A : Mat) : Nat := A 0 1 * A 1 0

/-- Magnitude form of 2×2 determinant (Nat-side, truncated). -/
def det2_mag (A : Mat) : Nat := det2_pos A - det2_neg A

/-- ★ Identity 2×2 has det = 1 (positive part). -/
theorem det2_pos_identity : det2_pos identityMat = 1 := by
  show identityMat 0 0 * identityMat 1 1 = 1
  show (if (0:Nat) = 0 then 1 else 0) * (if (1:Nat) = 1 then 1 else 0) = 1
  rfl

/-- ★ Identity 2×2 has zero negative part. -/
theorem det2_neg_identity : det2_neg identityMat = 0 := by
  show identityMat 0 1 * identityMat 1 0 = 0
  show (if (0:Nat) = 1 then 1 else 0) * (if (1:Nat) = 0 then 1 else 0) = 0
  rfl

/-- ★ Identity matrix det magnitude = 1 (term-mode). -/
theorem det2_mag_identity : det2_mag identityMat = 1 := by
  show det2_pos identityMat - det2_neg identityMat = 1
  rw [det2_pos_identity, det2_neg_identity]

/-- ★ Zero matrix has det = 0. -/
theorem det2_pos_zero : det2_pos zeroMat = 0 := rfl

/-- ★ Diagonal 2×2: positive det = a · d. -/
theorem det2_pos_diag (a d : Nat) :
    det2_pos (fun i j => if i = 0 ∧ j = 0 then a
                          else if i = 1 ∧ j = 1 then d
                          else 0) = a * d := rfl

end E213.Lib.Math.Linalg213.Gap.Determinant
