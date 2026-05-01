import E213.Research.Cauchy.Archimedean

/-!
# Research.Real213CutSum: cut-level addition (F1 of E5)

F1 from `E5_213_stays_213.md`: orderProj-native arithmetic.  Direct
sum definition on RealCut — bounded search over rational decomposition.

## Definition

`cutSum cx cy m k` := ∃ m1 ∈ [0, 2m] with cx(m1, 2k) ∧ cy(2m - m1, 2k).

= "existence of a *split* witness for limit_x + limit_y ≤ m/k".

## Significance

First step of 213-native arithmetic.  Direct cut-level work instead
of sequence-level lift (E2-E4 walls) — no Bishop ε-N machinery.

When `cx`, `cy` are cuts of Real213, `cutSum cx cy` is the cut of
their sum.  The ε/2 trick (k1 = k2 = 2k) is an *implementation
detail*; the primitive is bounded search.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy

/-- Bounded search: whether there exists m1 ∈ [0, m1Max] such that
    cx m1 (2k) ∧ cy (m1Max - m1) (2k). -/
def cutSumAux (cx cy : Nat → Nat → Bool) (k m1Max : Nat) : Nat → Bool
  | 0 => cx 0 (2*k) && cy m1Max (2*k)
  | n+1 => (cx (n+1) (2*k) && cy (m1Max - (n+1)) (2*k))
            || cutSumAux cx cy k m1Max n

/-- **cutSum**: sum cut of two cuts.  Bounded search over m1 ∈ [0, 2m]. -/
def cutSum (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  cutSumAux cx cy k (2*m) (2*m)

end E213.Research.Real213.CutSum
