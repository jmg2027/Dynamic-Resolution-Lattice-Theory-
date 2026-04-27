import E213.Hypervisor.Lens
import E213.Research.DiagonalClassification

/-!
# Research.NegSqLens: diagonal classification 의 5번째 범주

Note 35 의 4분류 (Collapse / Idempotent / Escalate / Multiply)
는 완전하지 않음.  Bool 에서 **sq = negation** (involution)
을 주는 combine 이 존재:

```
def negSqLens.combine u v := if u = v then !u else true
```

- `combine v v = !v` → sq 는 negation 함수.
- 그 어느 4범주에도 속하지 않음.

§5 "본질은 4 + special case" 가 맞음 — special case 중 하나.

## 구조적 해석

sq 는 involution: `sq (sq v) = v`.  Bool 의 `not` 함수.
4분류는 `sq` 가 constant / id / linear / quadratic 인 경우;
involution 은 제 5의 가능성.
-/

namespace E213.Research.NegSqLens

open E213.Firmware E213.Hypervisor E213.Research.DiagonalClassification

/-- Negation-sq Lens on Bool.  대각에서 !v, 대각 외에서 true. -/
def negSqLens : Lens Bool where
  base_a := false
  base_b := true
  combine u v := if u = v then !u else true

/-- sq negSqLens v = !v (negation). -/
theorem negSqLens_sq (v : Bool) : sq negSqLens v = !v := by
  cases v <;> rfl

/-- negSqLens 는 Idempotent 가 아님 (sq v = !v ≠ v). -/
theorem negSqLens_not_idempotent : ¬ Idempotent negSqLens := by
  intro h
  have : (!true : Bool) = true := h true
  cases this

/-- negSqLens 는 어떤 e 에 대해서도 Collapse 가 아님
    (sq 가 non-constant). -/
theorem negSqLens_not_collapse : ¬ ∃ e : Bool, Collapse negSqLens e := by
  intro ⟨e, hC⟩
  have h1 : (!true : Bool) = e := hC true
  have h2 : (!false : Bool) = e := hC false
  have hfalse : (!true : Bool) = false := rfl
  have htrue : (!false : Bool) = true := rfl
  rw [hfalse] at h1
  rw [htrue] at h2
  rw [← h1] at h2
  cases h2

/-- combine 은 symmetric (Lens 의 AXIOM 준수 요건). -/
theorem negSqLens_symmetric :
    ∀ u v : Bool, negSqLens.combine u v = negSqLens.combine v u := by
  intro u v; cases u <;> cases v <;> rfl

end E213.Research.NegSqLens
