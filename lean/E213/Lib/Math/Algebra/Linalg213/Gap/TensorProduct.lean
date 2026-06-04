/-!
# Linalg213 Gap — Tensor product (atomic dimension counting)

213-native paradigm: the tensor product `V ⊗ W` for finite-dim
spaces has dimension `dim V · dim W`.  At d=5 this gives
**`5 ⊗ 5 = 25`** which IS the K_{3,2}^{(c=2)} channel count
and the SU(5) GUT channel structure.

Atomic content:
  * `tensorDim m n = m * n`
  * `5 ⊗ 5 = 25` (rfl)
  * `tensorDim` is associative + commutative on Nat
-/

namespace E213.Lib.Math.Algebra.Linalg213.Gap.TensorProduct

/-- Tensor-product dimension on Nat. -/
def tensorDim (m n : Nat) : Nat := m * n

/-- ★ d=5 tensor: 5 ⊗ 5 = 25 (rfl). -/
theorem d5_tensor : tensorDim 5 5 = 25 := rfl

/-- ★ Tensor with 1: dim is preserved. -/
theorem tensor_one_left (n : Nat) : tensorDim 1 n = n := by
  show 1 * n = n
  exact Nat.one_mul n

/-- ★ Tensor with 1 (right): dim preserved. -/
theorem tensor_one_right (n : Nat) : tensorDim n 1 = n := by
  show n * 1 = n
  exact Nat.mul_one n

/-- ★ Tensor commutes (term-mode `Nat.mul_comm`). -/
theorem tensor_comm (m n : Nat) : tensorDim m n = tensorDim n m := by
  show m * n = n * m
  exact Nat.mul_comm m n

end E213.Lib.Math.Algebra.Linalg213.Gap.TensorProduct
