import E213.Research.ArchimedeanCauchy

/-!
# Research.Real213CutBinary: generic 2D bounded-search cut operation

User directive (2026-04-26): "Generic 으로 213 스럽게 가보자".

cutSum, cutMul 의 *공통 패턴* 추 출 — 2D bounded search over rational
witnesses.  Differences only in (1) precision factors (k1, k2), (2)
search bounds (M1, M2), (3) per-cell predicate.

## 정의

```
cutBinary P k1 k2 M1 M2 cx cy
  := ∃ m1 ≤ M1, m2 ≤ M2,
       P m1 m2 = true ∧ cx(m1, k1) = true ∧ cy(m2, k2) = true
```

## 213-style 의 의의

- **모든 binary cut operation 의 universal kernel** — Lens-style
  unified abstraction.
- cutSum, cutMul 등 specific operations = `cutBinary` 의 specific
  predicate / precision / bound 의 instance.
- locally-determined property 자동 유 도 (predicate 가 cx, cy 와
  무 관 하 게 정의 되 면).

## 의의

CutOp 의 *cardinality* 는 (predicate, k1, k2, M1, M2) 의 4D parameter
space — 모든 합 리 적 binary operation 이 이 안.  Bishop 의
ε-precision 선 택 도 이 안 의 special form.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- Inner loop: m2 ∈ [0, n], m1 fixed. -/
def cutBinaryInner (P : Nat → Nat → Bool) (k1 k2 : Nat)
    (cx cy : Nat → Nat → Bool) (m1 : Nat) : Nat → Bool
  | 0 => P m1 0 && cx m1 k1 && cy 0 k2
  | n+1 => (P m1 (n+1) && cx m1 k1 && cy (n+1) k2)
            || cutBinaryInner P k1 k2 cx cy m1 n

/-- Outer loop: m1 ∈ [0, n], m2 ∈ [0, M2]. -/
def cutBinaryOuter (P : Nat → Nat → Bool) (k1 k2 M2 : Nat)
    (cx cy : Nat → Nat → Bool) : Nat → Bool
  | 0 => cutBinaryInner P k1 k2 cx cy 0 M2
  | n+1 => cutBinaryInner P k1 k2 cx cy (n+1) M2
            || cutBinaryOuter P k1 k2 M2 cx cy n

/-- **Generic cutBinary**: 2D bounded search with predicate. -/
def cutBinary (P : Nat → Nat → Bool) (k1 k2 M1 M2 : Nat)
    (cx cy : Nat → Nat → Bool) : Bool :=
  cutBinaryOuter P k1 k2 M2 cx cy M1

end E213.Research.Real213CutSum

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- Inner congruence — m1 fixed, m2 iterated. -/
theorem cutBinaryInner_congr (P : Nat → Nat → Bool) (k1 k2 m1 M2 : Nat)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cx1 m1 k1 = cx2 m1 k1)
    (hy : ∀ m', m' ≤ M2 → cy1 m' k2 = cy2 m' k2)
    (n : Nat) (hn : n ≤ M2) :
    cutBinaryInner P k1 k2 cx1 cy1 m1 n
    = cutBinaryInner P k1 k2 cx2 cy2 m1 n := by
  induction n with
  | zero =>
    show (P m1 0 && cx1 m1 k1 && cy1 0 k2)
       = (P m1 0 && cx2 m1 k1 && cy2 0 k2)
    rw [hx, hy 0 (Nat.zero_le _)]
  | succ i ih =>
    have hi : i ≤ M2 := Nat.le_of_succ_le hn
    show ((P m1 (i+1) && cx1 m1 k1 && cy1 (i+1) k2)
            || cutBinaryInner P k1 k2 cx1 cy1 m1 i)
       = ((P m1 (i+1) && cx2 m1 k1 && cy2 (i+1) k2)
            || cutBinaryInner P k1 k2 cx2 cy2 m1 i)
    rw [hx, hy (i+1) hn, ih hi]

end E213.Research.Real213CutSum

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- Outer congruence — m1 iterated. -/
theorem cutBinaryOuter_congr (P : Nat → Nat → Bool) (k1 k2 M1 M2 : Nat)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : ∀ m', m' ≤ M1 → cx1 m' k1 = cx2 m' k1)
    (hy : ∀ m', m' ≤ M2 → cy1 m' k2 = cy2 m' k2)
    (n : Nat) (hn : n ≤ M1) :
    cutBinaryOuter P k1 k2 M2 cx1 cy1 n
    = cutBinaryOuter P k1 k2 M2 cx2 cy2 n := by
  induction n with
  | zero =>
    show cutBinaryInner P k1 k2 cx1 cy1 0 M2
       = cutBinaryInner P k1 k2 cx2 cy2 0 M2
    exact cutBinaryInner_congr P k1 k2 0 M2 cx1 cx2 cy1 cy2
            (hx 0 (Nat.zero_le _)) hy M2 (Nat.le_refl _)
  | succ i ih =>
    have hi : i ≤ M1 := Nat.le_of_succ_le hn
    show (cutBinaryInner P k1 k2 cx1 cy1 (i+1) M2
            || cutBinaryOuter P k1 k2 M2 cx1 cy1 i)
       = (cutBinaryInner P k1 k2 cx2 cy2 (i+1) M2
            || cutBinaryOuter P k1 k2 M2 cx2 cy2 i)
    have step1 := cutBinaryInner_congr P k1 k2 (i+1) M2 cx1 cx2 cy1 cy2
                    (hx (i+1) hn) hy M2 (Nat.le_refl _)
    rw [step1, ih hi]

/-- **Generic cutBinary 의 locally-determined property**. -/
theorem cutBinary_locallyDetermined (P : Nat → Nat → Bool) (k1 k2 M1 M2 : Nat)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : ∀ m', m' ≤ M1 → cx1 m' k1 = cx2 m' k1)
    (hy : ∀ m', m' ≤ M2 → cy1 m' k2 = cy2 m' k2) :
    cutBinary P k1 k2 M1 M2 cx1 cy1 = cutBinary P k1 k2 M1 M2 cx2 cy2 := by
  show cutBinaryOuter P k1 k2 M2 cx1 cy1 M1
     = cutBinaryOuter P k1 k2 M2 cx2 cy2 M1
  exact cutBinaryOuter_congr P k1 k2 M1 M2 cx1 cx2 cy1 cy2 hx hy M1 (Nat.le_refl _)

end E213.Research.Real213CutSum
