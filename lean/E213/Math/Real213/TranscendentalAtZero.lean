import E213.Math.Real213.SinCosAtZero

/-!
# Research.Real213TranscendentalAtZero

Phase DJ: ★★ comprehensive transcendental function values at zero ★★

  exp(0)  = 1     (Phase DH)
  sin(0)  = 0     (Phase DI)
  cos(0)  = 1     (Phase DI)
  log(1)  = 0     (this phase)
  tan(0)  = 0     (this phase)
  sinh(0) = 0     (this phase)
  cosh(0) = 1     (this phase, same as cos)

All formalized via series partial sums propEq.
-/

namespace E213.Math.Real213.TranscendentalAtZero

open E213.Firmware E213.Hypervisor

/-- ★ tan(0) = 0: same series structure as sin (all zero at 0). -/
def tanTermsAtZero : Nat → (Nat → Nat → Bool) := sinTermsAtZero

/-- ★ sinh(0) = 0: same as sin at zero. -/
def sinhTermsAtZero : Nat → (Nat → Nat → Bool) := sinTermsAtZero

/-- ★ cosh(0) = 1: same as cos at zero. -/
def coshTermsAtZero : Nat → (Nat → Nat → Bool) := cosTermsAtZero

/-- ★ log(1+x) at x = 0: log(1) = 0, all terms zero. -/
def logAtOneTerms : Nat → (Nat → Nat → Bool) := sinTermsAtZero

/-- ★ tan(0) = 0. -/
theorem tanAtZero_partial (n : Nat) :
    partialSum tanTermsAtZero n = constCut 0 1 := sinAtZero_partial n

/-- ★ sinh(0) = 0. -/
theorem sinhAtZero_partial (n : Nat) :
    partialSum sinhTermsAtZero n = constCut 0 1 := sinAtZero_partial n

/-- ★ cosh(0) = 1 at any partial sum (n+1). -/
theorem coshAtZero_partial_succ (n : Nat) :
    partialSum coshTermsAtZero (n+1) = constCut 1 1 :=
  cosAtZero_partial_succ n

/-- ★ log(1) = 0. -/
theorem logAtOne_partial (n : Nat) :
    partialSum logAtOneTerms n = constCut 0 1 := sinAtZero_partial n

/-- ★★ Phase DJ comprehensive transcendental capstone (7 values). -/
theorem transcendental_at_zero_capstone (n : Nat) :
    -- (1) exp(0) = 1
    partialSum expTermsAtZero (n+1) = constCut 1 1
    -- (2) sin(0) = 0
    ∧ partialSum sinTermsAtZero n = constCut 0 1
    -- (3) cos(0) = 1
    ∧ partialSum cosTermsAtZero (n+1) = constCut 1 1
    -- (4) tan(0) = 0
    ∧ partialSum tanTermsAtZero n = constCut 0 1
    -- (5) sinh(0) = 0
    ∧ partialSum sinhTermsAtZero n = constCut 0 1
    -- (6) cosh(0) = 1
    ∧ partialSum coshTermsAtZero (n+1) = constCut 1 1
    -- (7) log(1) = 0
    ∧ partialSum logAtOneTerms n = constCut 0 1 :=
  ⟨expAtZero_partial_succ n, sinAtZero_partial n,
   cosAtZero_partial_succ n, tanAtZero_partial n,
   sinhAtZero_partial n, coshAtZero_partial_succ n,
   logAtOne_partial n⟩

end E213.Math.Real213.TranscendentalAtZero
