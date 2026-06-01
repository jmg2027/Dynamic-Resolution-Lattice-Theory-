import E213.Lib.Math.Linalg213.Gap.MatrixMul
import E213.Lib.Math.Linalg213.Gap.Determinant
import E213.Lib.Math.Linalg213.Gap.TensorProduct
import E213.Lib.Math.Linalg213.Gap.Eigen

/-!
# Linalg213 Gap — Capstone synthesis

5 cluster witnesses + total bundle.  All ∅-axiom.

Companion to the existing Linalg213 paper-1 Capstone (chiral
compression).  This bundle covers elementary linear-algebra
operations (matrix multiplication, determinant, tensor product,
eigenvalue) that the paper-1 capstone leaves at structure level.
-/

namespace E213.Lib.Math.Linalg213.Gap.Capstone

open E213.Lib.Math.Linalg213.Gap.MatrixMul
  (Mat identityMat zeroMat matMul_zero_dim zero_mul_any)
open E213.Lib.Math.Linalg213.Gap.Determinant
  (det2_pos det2_neg det2_mag det2_pos_identity det2_neg_identity
   det2_mag_identity det2_pos_zero)
open E213.Lib.Math.Linalg213.Gap.TensorProduct
  (tensorDim d5_tensor tensor_one_left tensor_comm)
open E213.Lib.Math.Linalg213.Gap.Eigen
  (scalar_eigen_e0 identity_eigen_one)

/-- ★★★ **Total witness** ★★★ — full bundle covering matrix
    multiplication, determinant, tensor, eigenvalue.

    Folds in the four earlier per-cluster witnesses (matrixMul,
    determinant, tensor, eigen) plus the original headline facts. -/
theorem total_witness (lam v0 m n : Nat) (A B : Mat) (i j : Nat) :
    -- Matrix multiplication
    E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 0 A B i j = 0
    ∧ E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 3 zeroMat B i j = 0
    -- Determinant
    ∧ det2_pos identityMat = 1
    ∧ det2_neg identityMat = 0
    ∧ det2_mag identityMat = 1
    ∧ det2_pos zeroMat = 0
    -- Tensor product
    ∧ tensorDim 5 5 = 25
    ∧ tensorDim 1 n = n
    ∧ tensorDim m n = tensorDim n m
    -- Eigenvalue
    ∧ E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 1
        (E213.Lib.Math.Linalg213.Gap.Eigen.scalarMat lam)
        (fun k _ => if k = 0 then 1 else 0) 0 0 = lam
    ∧ E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 1
        identityMat (fun _ _ => v0) 0 0 = v0 :=
  ⟨ matMul_zero_dim A B i j, zero_mul_any 3 B i j
  , det2_pos_identity, det2_neg_identity, det2_mag_identity, det2_pos_zero
  , d5_tensor, tensor_one_left n, tensor_comm m n
  , scalar_eigen_e0 lam, identity_eigen_one v0 ⟩

end E213.Lib.Math.Linalg213.Gap.Capstone
