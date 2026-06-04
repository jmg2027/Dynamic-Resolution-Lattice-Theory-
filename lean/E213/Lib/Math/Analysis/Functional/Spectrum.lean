import E213.Lib.Math.Analysis.Functional.LinearOperator
import E213.Meta.Tactic.NatHelper

/-!
# Functional Analysis 213 — Spectrum (atomic, finite-grid)

213-native paradigm: an *eigenpair* `(λ, v)` for `T` is a pointwise
identity `T v i = λ * v i`.  No general spectral theorem chase
(Choice / Banach algebra completion rejected).  Closed-form atomic
witnesses for the elementary cases.

Atomic content:
  * `idOp` has eigenvalue 1 (every vector is an eigenvector).
  * `scaleOp c` has eigenvalue `c` (every vector).
  * `zeroOp` has eigenvalue 0 (every vector).
-/

namespace E213.Lib.Math.Analysis.Functional.Spectrum

open E213.Lib.Math.Analysis.Functional.LinearOperator
  (LinOp idOp zeroOp scaleOp composeOp)

/-- `IsEigenpair T λ v` (pointwise on `Nat → Nat`). -/
def IsEigenpair (T : LinOp) (lam : Nat) (v : Nat → Nat) : Prop :=
  ∀ i, T v i = lam * v i

/-- ★ Identity has eigenvalue 1, every vector. -/
theorem id_eigen (v : Nat → Nat) : IsEigenpair idOp 1 v := by
  intro i
  show v i = 1 * v i
  exact (Nat.one_mul (v i)).symm

/-- ★ Scale operator has eigenvalue `c`, every vector. -/
theorem scale_eigen (c : Nat) (v : Nat → Nat) :
    IsEigenpair (scaleOp c) c v := fun _ => rfl

/-- ★ Zero operator has eigenvalue 0, every vector. -/
theorem zero_eigen (v : Nat → Nat) : IsEigenpair zeroOp 0 v := by
  intro i
  show 0 = 0 * v i
  exact (Nat.zero_mul (v i)).symm

/-- ★ Composition: `(scaleOp a) ∘ (scaleOp b)` has eigenvalue `a · b`. -/
theorem compose_scale_eigen (a b : Nat) (v : Nat → Nat) :
    IsEigenpair (composeOp (scaleOp a) (scaleOp b)) (a * b) v := by
  intro i
  show a * (b * v i) = a * b * v i
  exact (E213.Tactic.NatHelper.mul_assoc a b (v i)).symm

end E213.Lib.Math.Analysis.Functional.Spectrum
