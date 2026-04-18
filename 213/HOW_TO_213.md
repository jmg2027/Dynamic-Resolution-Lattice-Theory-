# 213으로 Lean 작성하는 법

## 원칙

213에는 타입이 없다. Lean에는 타입이 있다.
이것은 매체의 제약이다. 타입을 하나만 쓴다.

## 규칙

### 1. 타입은 E 하나

```lean
inductive E where
  | e1 : E    -- 경계 (0)
  | e2 : E    -- 내용 1
  | e3 : E    -- 내용 2
```

다른 inductive를 만들어도 되지만,
213의 내용이 아니라 매체의 도구임을 명시한다.

### 2. 표현식은 Expr

```lean
inductive Expr where
  | atom : E → Expr
  | plus : Expr → Expr → Expr    -- 1이 사이에 있음
  | times : Expr → Expr → Expr   -- 1이 사이에 없음
```

### 3. 동치는 Equiv (공리 기반) 또는 normalize (런타임 기반)

**공리 기반 (e213 223.lean 스타일):**
```lean
inductive Equiv : Expr → Expr → Prop where
  -- 매체 비용 9개 + 고유 3개 = 12개
```
증명은 `Equiv.trans`, `Equiv.plus_comm` 등으로 체인.

**런타임 기반 (e213 runtime.lean 스타일):**
```lean
structure Term where
  p : Nat    -- e₂ 차수
  q : Nat    -- e₃ 차수

def normalize : Expr → List Term
```
동치 판정: `normalize a == normalize b`.
교환/결합/분배가 자동.

### 4. 편의 표기

```lean
def e₁ := Expr.atom .e1
def e₂ := Expr.atom .e2
def e₃ := Expr.atom .e3
```

### 5. eval은 관찰용

```lean
def eval : E → Nat
  | .e1 => 0
  | .e2 => 2
  | .e3 => 3
```

eval은 213 안이 아니라 밖이다.
`#eval`로 확인하되, 증명에 쓰지 않는다 (쓰면 Nat 의존).

### 6. 주석 규칙

매체의 도구를 쓸 때 명시한다:

```lean
-- [매체] List는 순서가 있다. 213에는 순서가 없다.
-- [213] 이 정리는 213의 내재적 성질이다.
-- [eval] 이 값은 eval(2,3) 특수이다.
```

## 파일 구조

| 접근 | 파일 | 특징 |
|------|------|------|
| 공리 기반 | e213 223.lean | 12공리. 증명은 Equiv 체인. |
| 런타임 | e213 runtime.lean | 0공리. normalize로 판정. |
| 자체 Nat | e213 scratch.lean | Tally로 Nat 대체. |
| 혼합 | e213.lean | Nat eval로 수치 확인. |

## 실험 방법

### A. 새 동치 확인

```lean
-- 공리 기반:
theorem my_result : plus e₂ (times e₃ e₃) ≈
    plus (times e₃ e₃) e₂ :=
  Equiv.plus_comm _ _

-- 런타임 기반:
#eval equivDecide
  (plus e₂ (times e₃ e₃))
  (plus (times e₃ e₃) e₂)  -- true
```

### B. 새 모델 구성 (독립성 등)

```lean
-- 3원소 모델로 공리 위반 확인
inductive S where | a | b | c
def my_plus : S → S → S := ...
def my_times : S → S → S := ...
-- 특정 공리가 실패함을 decide로 확인
theorem breaks_A12 : ... ≠ ... := by decide
```

### C. 새 불변량 계산

```lean
-- 다항식 수준에서 계산
def my_poly : Poly := Poly.x.mul Poly.x  -- x²
#eval my_poly.eval 2 3   -- 4
#eval my_poly == my_poly.swap  -- x²↔y² 대칭?
```

### D. Cayley-Dickson 양립성

```lean
-- 새 대수의 213 양립성 확인
def MyAlgebra.compatible213 : Bool :=
  !hasOrder && hasComm && hasAssoc
```

## import 규칙

| 필요한 것 | import |
|----------|--------|
| 순수 213 (공리 증명) | 없음 또는 자체 파일 |
| 수치 확인 (#eval) | `import Init` |
| 정렬, 리스트 | `import Init` |
| ζ(2), π | `import Mathlib.NumberTheory.ZetaValues` |
| decide, omega | `import Init` |

## 요약

```
1. E 하나, Expr 하나.
2. 공리 기반이면 Equiv로 증명.
3. 런타임이면 normalize로 판정.
4. eval은 밖. 주석으로 명시.
5. 매체 도구는 [매체]로 표기.
```
