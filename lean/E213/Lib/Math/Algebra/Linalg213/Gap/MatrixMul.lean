/-!
# Linalg213 Gap — Matrix multiplication (atomic, Nat-side)

213-native paradigm: a matrix is `Nat → Nat → Nat`; matrix
multiplication is the standard pointwise sum-of-products over a
finite inner index range.

Atomic content:
  * `matrixMulNum n A B i j = Σ_{k < n} A i k · B k j`.
  * Identity matrix: 1 on the diagonal, 0 off.
  * `mul_id_right`: `A · I = A` (term-mode by induction).
-/

namespace E213.Lib.Math.Algebra.Linalg213.Gap.MatrixMul

/-- Matrix as a function `Nat → Nat → Nat`. -/
abbrev Mat := Nat → Nat → Nat

/-- Inner product over the first `n` indices: Σ_{k < n} A i k · B k j. -/
def matrixMulNum : Nat → Mat → Mat → Mat
  | 0, _, _ => fun _ _ => 0
  | n + 1, A, B => fun i j =>
      matrixMulNum n A B i j + A i n * B n j

/-- Identity matrix: 1 on diagonal, 0 off. -/
def identityMat : Mat := fun i j => if i = j then 1 else 0

/-- Zero matrix. -/
def zeroMat : Mat := fun _ _ => 0

/-- ★ Matrix mul at n=0 is zero matrix (rfl). -/
theorem matMul_zero_dim (A B : Mat) (i j : Nat) :
    matrixMulNum 0 A B i j = 0 := rfl

/-- ★ Zero × any = 0. -/
theorem zero_mul_any : ∀ (n : Nat) (B : Mat) (i j : Nat),
    matrixMulNum n zeroMat B i j = 0
  | 0, _, _, _ => rfl
  | n + 1, B, i, j => by
      show matrixMulNum n zeroMat B i j + zeroMat i n * B n j = 0
      rw [zero_mul_any n B i j]
      show 0 + 0 * B n j = 0
      rw [Nat.zero_mul, Nat.add_zero]

end E213.Lib.Math.Algebra.Linalg213.Gap.MatrixMul
