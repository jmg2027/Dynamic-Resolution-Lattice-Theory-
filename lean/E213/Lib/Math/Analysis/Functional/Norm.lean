/-!
# Functional Analysis 213 — Norm (atomic, finite-grid)

213-native paradigm: a *norm* on `Nat → Nat` is the maximum value
over a finite index range.  No completion-by-Cauchy chase — the
finite grid IS the norm's domain at this resolution.

Atomic content:
  * `lInfNorm n f` — `sup_{i < n} f i` (Nat-side, computable).
  * `l1Norm n f` — `Σ_{i < n} f i`.
  * Constant function: `‖const c‖_∞ = c`, `‖const c‖_1 = n · c`.
-/

namespace E213.Lib.Math.Analysis.Functional.Norm

/-- L∞ norm over the first `n` indices: max of `f 0`, …, `f (n-1)`. -/
def lInfNorm : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => Nat.max (lInfNorm n f) (f n)

/-- L¹ norm over the first `n` indices: sum. -/
def l1Norm : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => l1Norm n f + f n

/-- Constant function. -/
def constFn (c : Nat) : Nat → Nat := fun _ => c

/-- ★ L∞ at n = 0 is 0 (rfl). -/
theorem lInf_zero (f : Nat → Nat) : lInfNorm 0 f = 0 := rfl

/-- ★ L¹ at n = 0 is 0 (rfl). -/
theorem l1_zero (f : Nat → Nat) : l1Norm 0 f = 0 := rfl

/-- ★ L¹ of constant `c` over `n` cells = `n · c`. -/
theorem l1_const : ∀ (n c : Nat),
    l1Norm n (constFn c) = n * c
  | 0, c => by
      show 0 = 0 * c
      exact (Nat.zero_mul c).symm
  | n + 1, c => by
      show l1Norm n (constFn c) + c = (n + 1) * c
      rw [l1_const n c]
      show n * c + c = (n + 1) * c
      exact (Nat.succ_mul n c).symm

/-- ★ L∞ at `n = 1` is `f 0`. -/
theorem lInf_one (f : Nat → Nat) :
    lInfNorm 1 f = f 0 := by
  show Nat.max (lInfNorm 0 f) (f 0) = f 0
  show Nat.max 0 (f 0) = f 0
  exact Nat.zero_max (f 0)

end E213.Lib.Math.Analysis.Functional.Norm
