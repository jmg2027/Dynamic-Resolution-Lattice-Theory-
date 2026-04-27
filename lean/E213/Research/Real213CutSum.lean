import E213.Research.ArchimedeanCauchy

/-!
# Research.Real213CutSum: cut-level addition (E5 의 F1)

`E5_213_stays_213.md` 의 F1: orderProj-native arithmetic.  RealCut 위
직접 sum 정의 — bounded search over rational decomposition.

## 정의

`cutSum cx cy m k` := ∃ m1 ∈ [0, 2m] with cx(m1, 2k) ∧ cy(2m - m1, 2k).

= "limit_x + limit_y ≤ m/k 의 *쪼개 진* witness 존재".

## 의의

213-native arithmetic 의 첫 step.  Sequence-level lift (E2-E4 walls)
대 신 cut-level 직접 작업 — Bishop ε-N machinery 부재.

`cx`, `cy` 가 Real213 의 cut 일 때, `cutSum cx cy` 가 합 의 cut.
ε/2 trick (k1 = k2 = 2k) 는 *implementation detail*, primitive 는
bounded search.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy

/-- Bounded search: m1 ∈ [0, m1Max] 중 cx m1 (2k) ∧ cy (m1Max - m1) (2k)
    인 m1 존재 여부. -/
def cutSumAux (cx cy : Nat → Nat → Bool) (k m1Max : Nat) : Nat → Bool
  | 0 => cx 0 (2*k) && cy m1Max (2*k)
  | n+1 => (cx (n+1) (2*k) && cy (m1Max - (n+1)) (2*k))
            || cutSumAux cx cy k m1Max n

/-- **cutSum**: 두 cut 의 sum cut.  Bounded search over m1 ∈ [0, 2m]. -/
def cutSum (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  cutSumAux cx cy k (2*m) (2*m)

end E213.Research.Real213CutSum
