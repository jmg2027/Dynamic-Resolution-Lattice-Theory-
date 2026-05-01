import E213.Research.Real213.ExpAtZero

/-!
# Research.Real213SinCosAtZero

Phase DI: ★★ sin(0) = 0, cos(0) = 1 — trigonometric values propEq ★★

For sin(x) = Σ (-1)^n x^(2n+1) / (2n+1)!:
  sin(0) = 0 + 0 + 0 + ... = 0

For cos(x) = Σ (-1)^n x^(2n) / (2n)!:
  cos(0) = 1 + 0 + 0 + ... = 1 (same as exp at 0)

Both formalized via series partial sums.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- ★ sin series terms at x = 0: all zero. -/
def sinTermsAtZero : Nat → (Nat → Nat → Bool) :=
  fun _ => constCut 0 1

/-- ★ cos series terms at x = 0: only n=0 term is 1. -/
def cosTermsAtZero : Nat → (Nat → Nat → Bool)
  | 0 => constCut 1 1
  | _+1 => constCut 0 1

/-- ★ partialSum sinTermsAtZero n = 0 for all n. -/
theorem sinAtZero_partial (n : Nat) :
    partialSum sinTermsAtZero n = constCut 0 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show cutSum (partialSum sinTermsAtZero k) (sinTermsAtZero k) = constCut 0 1
    rw [ih]
    show cutSum (constCut 0 1) (constCut 0 1) = constCut 0 1
    exact cutSum_zero_zero

/-- ★ cos(0) = 1 via series (same as exp). -/
theorem cosAtZero_partial_succ (n : Nat) :
    partialSum cosTermsAtZero (n+1) = constCut 1 1 := by
  induction n with
  | zero =>
    show cutSum (constCut 0 1) (cosTermsAtZero 0) = constCut 1 1
    show cutSum (constCut 0 1) (constCut 1 1) = constCut 1 1
    exact cutSum_zero_const 1 1
  | succ k ih =>
    show cutSum (partialSum cosTermsAtZero (k+1)) (cosTermsAtZero (k+1))
         = constCut 1 1
    rw [ih]
    show cutSum (constCut 1 1) (constCut 0 1) = constCut 1 1
    exact cutSum_const_zero 1 1

/-- ★★ Phase DI capstone: sin(0) = 0, cos(0) = 1 propEq. -/
theorem sinCosAtZero_capstone (n : Nat) :
    -- (1) sin(0) = 0 at any partial sum
    partialSum sinTermsAtZero n = constCut 0 1
    -- (2) cos(0) = 1 (n+1 partial sum)
    ∧ partialSum cosTermsAtZero (n+1) = constCut 1 1 :=
  ⟨sinAtZero_partial n, cosAtZero_partial_succ n⟩

end E213.Research.Real213.CutSum
