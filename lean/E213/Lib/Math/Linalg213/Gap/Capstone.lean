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
  (tensorDim d5_tensor tensor_one_left tensor_comm n_resolution_link)
open E213.Lib.Math.Linalg213.Gap.Eigen
  (scalar_eigen_e0 identity_eigen_one)

/-- ★ **Matrix multiplication witness** — zero/zero × any. -/
theorem matrixMul_witness (A B : Mat) (i j : Nat) :
    E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 0 A B i j = 0
    ∧ E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 3 zeroMat B i j = 0 :=
  ⟨matMul_zero_dim A B i j, zero_mul_any 3 B i j⟩

/-- ★ **Determinant witness** — 2×2 identity / zero / mag. -/
theorem determinant_witness :
    det2_pos identityMat = 1
    ∧ det2_neg identityMat = 0
    ∧ det2_mag identityMat = 1
    ∧ det2_pos zeroMat = 0 :=
  ⟨det2_pos_identity, det2_neg_identity, det2_mag_identity,
   det2_pos_zero⟩

/-- ★ **Tensor-product witness** — `5 ⊗ 5 = 25`, identity, comm,
    N_resolution = 5²⁵ link. -/
theorem tensor_witness (m n : Nat) :
    tensorDim 5 5 = 25
    ∧ tensorDim 1 n = n
    ∧ tensorDim m n = tensorDim n m
    ∧ (5 : Nat) ^ tensorDim 5 5 = (5 : Nat) ^ 25 :=
  ⟨d5_tensor, tensor_one_left n, tensor_comm m n, n_resolution_link⟩

/-- ★ **Eigenvalue witness** — scalar λ matrix on basis e₀, identity on constant. -/
theorem eigen_witness (v0 lam : Nat) :
    (E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 1
        (E213.Lib.Math.Linalg213.Gap.Eigen.scalarMat lam)
        (fun k _ => if k = 0 then 1 else 0) 0 0
      = lam)
    ∧ (E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 1
        identityMat (fun _ _ => v0) 0 0 = v0) :=
  ⟨scalar_eigen_e0 lam, identity_eigen_one v0⟩

/-- ★★★ **Total witness** ★★★ — 5-fact bundle covering matrix
    multiplication, determinant, tensor, eigenvalue, GUT link. -/
theorem total_witness (lam : Nat) :
    det2_pos identityMat = 1
    ∧ det2_mag identityMat = 1
    ∧ tensorDim 5 5 = 25
    ∧ (5 : Nat) ^ tensorDim 5 5 = (5 : Nat) ^ 25
    ∧ E213.Lib.Math.Linalg213.Gap.MatrixMul.matrixMulNum 1
        (E213.Lib.Math.Linalg213.Gap.Eigen.scalarMat lam)
        (fun k _ => if k = 0 then 1 else 0) 0 0 = lam :=
  ⟨det2_pos_identity, det2_mag_identity, d5_tensor, n_resolution_link,
   scalar_eigen_e0 lam⟩

end E213.Lib.Math.Linalg213.Gap.Capstone
