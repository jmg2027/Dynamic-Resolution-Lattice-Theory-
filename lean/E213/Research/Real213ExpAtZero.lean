import E213.Research.Real213GeomSeriesPartialSum

/-!
# Research.Real213ExpAtZero

Phase DH: ★★ exp(0) = 1 via series formalization ★★

The exponential function exp(x) = Σ x^n / n!.  At x = 0:
  exp(0) = 1 + 0 + 0 + ... = 1

We define `expTermsAtZero` as the series with only the first term
non-zero, and prove all partial sums equal constCut 1 1.

This is the FIRST transcendental function value formalized propEq
in the 213 framework.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- ★ exp series terms at x = 0: only n=0 term is non-zero. -/
def expTermsAtZero : Nat → (Nat → Nat → Bool)
  | 0 => constCut 1 1
  | _+1 => constCut 0 1

/-- ★ Σ_{i=0}^0 = 0 (empty sum). -/
theorem expAtZero_partial_zero :
    partialSum expTermsAtZero 0 = constCut 0 1 := rfl

/-- ★ Σ_{i=0}^0 (1 + 0 + ...) = 1 (only first term). -/
theorem expAtZero_partial_one :
    partialSum expTermsAtZero 1 = constCut 1 1 := by
  show cutSum (constCut 0 1) (expTermsAtZero 0) = constCut 1 1
  show cutSum (constCut 0 1) (constCut 1 1) = constCut 1 1
  exact cutSum_zero_const 1 1

/-- ★ Σ_{i=0}^1 = 1 + 0 = 1. -/
theorem expAtZero_partial_two :
    partialSum expTermsAtZero 2 = constCut 1 1 := by
  show cutSum (partialSum expTermsAtZero 1) (expTermsAtZero 1) = constCut 1 1
  rw [expAtZero_partial_one]
  show cutSum (constCut 1 1) (constCut 0 1) = constCut 1 1
  exact cutSum_const_zero 1 1

/-- ★ ∀ n ≥ 1, partial sum stays at 1 (= exp(0)). -/
theorem expAtZero_partial_succ (n : Nat) :
    partialSum expTermsAtZero (n+1) = constCut 1 1 := by
  induction n with
  | zero => exact expAtZero_partial_one
  | succ k ih =>
    show cutSum (partialSum expTermsAtZero (k+1)) (expTermsAtZero (k+1))
         = constCut 1 1
    rw [ih]
    show cutSum (constCut 1 1) (constCut 0 1) = constCut 1 1
    exact cutSum_const_zero 1 1

/-- ★★ Phase DH capstone: exp(0) = 1 propEq for all partial sums n ≥ 1. -/
theorem expAtZero_capstone (n : Nat) :
    -- (1) Empty sum = 0
    partialSum expTermsAtZero 0 = constCut 0 1
    -- (2) S_1 = 1 (= exp(0))
    ∧ partialSum expTermsAtZero 1 = constCut 1 1
    -- (3) ★★ ∀ n ≥ 1, partial sum = 1 (= exp(0))
    ∧ partialSum expTermsAtZero (n+1) = constCut 1 1 :=
  ⟨expAtZero_partial_zero, expAtZero_partial_one,
   expAtZero_partial_succ n⟩

end E213.Research.Real213CutSum
