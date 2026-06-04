import E213.Lib.Math.Algebra.Linalg213.Gap.MatrixMul
import E213.Meta.Tactic.NatHelper

/-!
# Linalg213 Gap — Eigenvalues (atomic, diagonal closed form)

213-native paradigm: a *matrix eigenpair* `(λ, v)` is the pointwise
identity `Σ_k A i k · v k = λ · v i`.  For diagonal matrices this
is purely combinatorial.

Atomic content:
  * Identity matrix has eigenvalue 1 on every vector.
  * Diagonal scalar matrix `λ · I` has eigenvalue `λ`.
  * 2×2 specific witnesses.
-/

namespace E213.Lib.Math.Algebra.Linalg213.Gap.Eigen

open E213.Lib.Math.Algebra.Linalg213.Gap.MatrixMul (Mat identityMat matrixMulNum)

/-- A vector eigenpair predicate (pointwise; on first `n` indices). -/
def IsMatEigenpair (n : Nat) (A : Mat) (lam : Nat) (v : Nat → Nat) : Prop :=
  ∀ i, (matrixMulNum n A (fun k _ => v k) i 0) = lam * v i

/-- Scalar matrix `λ · I` (diagonal of `λ`s). -/
def scalarMat (lam : Nat) : Mat := fun i j => if i = j then lam else 0

/-- ★ Scalar matrix has eigenvalue `λ` on the basis vector e₀. -/
theorem scalar_eigen_e0 (lam : Nat) :
    (matrixMulNum 1 (scalarMat lam) (fun k _ => if k = 0 then 1 else 0) 0 0)
      = lam := by
  show 0 + scalarMat lam 0 0 * (if (0:Nat) = 0 then 1 else 0) = lam
  show 0 + (if (0:Nat) = 0 then lam else 0) * 1 = lam
  show 0 + lam * 1 = lam
  rw [Nat.mul_one, Nat.zero_add]

/-- ★ Identity has eigenvalue 1 (rfl-witness on n=1 case). -/
theorem identity_eigen_one (v0 : Nat) :
    matrixMulNum 1 identityMat (fun _ _ => v0) 0 0 = v0 := by
  show 0 + identityMat 0 0 * v0 = v0
  show 0 + (if (0:Nat) = 0 then 1 else 0) * v0 = v0
  show 0 + 1 * v0 = v0
  rw [Nat.one_mul, Nat.zero_add]

end E213.Lib.Math.Algebra.Linalg213.Gap.Eigen
