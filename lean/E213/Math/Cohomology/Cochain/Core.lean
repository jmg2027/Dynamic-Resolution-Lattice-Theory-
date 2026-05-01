import E213.Physics.Simplex.Counts

/-!
# Cohomology — k-cochain type with ℤ/2 coefficients (Phase CA, file 1)

213-internal cochain complex foundation, Mathlib-free, 0 axiom.

`Cochain n k = Fin (binom n k) → Bool` — Bool-valued functions on
the i-th k-element subset of n vertices (i ∈ Fin (binom n k)).
ℤ/2 = Bool with XOR; coefficient (−1) is identity in ℤ/2.

This file defines the type + zero + add (XOR) only.
δ (coboundary) lives in `CohomologyDelta.lean` (file 3).
-/

namespace E213.Math.Cohomology.Cochain.Core

open E213.Physics.Simplex.Counts (binom d NS NT)

/-- k-cochain on Δⁿ⁻¹ (n vertices total): a function from k-th
    subsets to Bool.  Number of k-subsets = `binom n k`. -/
def Cochain (n k : Nat) : Type := Fin (binom n k) → Bool

namespace Cochain

/-- Zero cochain (XOR identity). -/
def zero (n k : Nat) : Cochain n k := fun _ => false

/-- Pointwise XOR (= mod-2 sum). -/
def add {n k : Nat} (σ τ : Cochain n k) : Cochain n k :=
  fun i => xor (σ i) (τ i)

/-- xor is involutive on Bool. -/
theorem xor_self_eq_false (b : Bool) : xor b b = false := by
  cases b <;> rfl

/-- xor with false is identity. -/
theorem xor_false_right (b : Bool) : xor b false = b := by
  cases b <;> rfl

/-- 2σ = 0 in ℤ/2. -/
theorem add_self {n k : Nat} (σ : Cochain n k) :
    ∀ i, add σ σ i = zero n k i := by
  intro i; show xor (σ i) (σ i) = false
  exact xor_self_eq_false (σ i)

/-- σ + 0 = σ. -/
theorem add_zero {n k : Nat} (σ : Cochain n k) :
    ∀ i, add σ (zero n k) i = σ i := by
  intro i; show xor (σ i) false = σ i
  exact xor_false_right (σ i)

/-- 0 + σ = σ. -/
theorem zero_add {n k : Nat} (σ : Cochain n k) :
    ∀ i, add (zero n k) σ i = σ i := by
  intro i; show xor false (σ i) = σ i
  cases σ i <;> rfl

/-- add is commutative. -/
theorem add_comm {n k : Nat} (σ τ : Cochain n k) :
    ∀ i, add σ τ i = add τ σ i := by
  intro i; show xor (σ i) (τ i) = xor (τ i) (σ i)
  cases σ i <;> cases τ i <;> rfl

end Cochain

/-! ## Concrete dimension table at d = 5 (Δ⁴ atomic) -/

theorem dim_C0 : binom d 0 = 1  := by decide
theorem dim_C1 : binom d 1 = 5  := by decide
theorem dim_C2 : binom d 2 = 10 := by decide
theorem dim_C3 : binom d 3 = 10 := by decide
theorem dim_C4 : binom d 4 = 5  := by decide
theorem dim_C5 : binom d 5 = 1  := by decide

end E213.Math.Cohomology.Cochain.Core
