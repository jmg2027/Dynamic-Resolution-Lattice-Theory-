# 47 — Lens kernel 공간 cardinality: bounds + conjecture

## Bounds

### Upper bound: 𝔠 (= 2^ℵ₀)

**증명 sketch**:
- Raw 는 countable (ℕ-equipotent, Σ2 Godel encoding).
- Raw 위의 equivalence relations ≤ 2^|Raw × Raw| = 2^ℵ₀ = 𝔠.
- Slash-congruences ⊆ equivalence relations.
- 따라서 Lens kernel 공간 ≤ 𝔠.

### Lower bound: ℵ₀ (countable 무한)

**증명**: Mod m family 가 countable 무한 distinct kernels
(`LeavesModNat.lean` + `refines_implies_divides` converse).

각 m, k ≥ 2 에 대해 `L_m` 과 `L_k` 의 kernel 이 distinct
iff m ≠ k (via divisibility).  ℕ≥2 가 countable 무한 →
countable 무한 distinct kernels.

## Open question

**Lens kernel 공간이 정확히 countable (ℵ₀) 인가, 𝔠 인가?**

현재 증명된 것은 upper = 𝔠, lower = ℵ₀.  실제 값은 미답.

## §1. Countable 후보 논증

**주장 (미증명)**: Lens kernel 공간은 countable.

**Intuition**:
- 각 kernel 은 Raw 의 slash-congruence.
- Slash-congruence 는 (Raw.a 의 class, Raw.b 의 class,
  combine 테이블) 의 세 부분으로 완전 결정.
- Raw / kernel 의 classes 는 countable (Raw 가 countable).
- Classes 간 combine 테이블은 countable domain × countable
  domain → countable codomain 의 함수.
- **그러나** 함수 공간 자체는 최대 𝔠.  이 부분이 bound 느슨.

"각 congruence 의 complete description 이 countable
information" 이어야 countable.  미확인.

## §2. Uncountable (𝔠) 후보 논증

**주장 (미증명)**: Lens kernel 공간은 𝔠.

**Construction 시도 (부분 성공)**:

For each function f : ℕ → ℕ with "fold compatibility" 조건:
정의된 combine 이 f(n) 을 계산하도록.

- f(n) = n % m: 각 m 이 distinct kernel.  Countable family.
- f(n) = n: leaves kernel.
- f(n) = specific non-linear: combine 이 잘 정의되려면 f(u+v)
  가 (f(u), f(v)) 로 결정되어야.  이는 f 가 additive-compatible
  이어야 하며, 이 조건이 f 를 **정확히 mod m family 로 한정**.

결과: countable 하한 (mod m) 이 실제로 상한 인 듯.  하지만
증명은 필요.

## §3. Bezout 와 유사한 argument

non-additive-compatible 한 kernel 을 찾으려면 **a-count 와
b-count 의 조합** 같은 것이 필요.

abLens family (parametrized by single Nat "weight"): L_n 의
view = a-count + n * b-count.  각 n ≥ 0 에 대해 distinct
kernel (note: 다른 노트에서 상세).

이것도 countable 무한.

**Non-linear 조합**: view = a-count × b-count? 
- combine (a1, b1)(a2, b2) = (a1+a2) × (b1+b2)?  
  하지만 combine 은 α × α → α 이고, α = Nat 이면 
  combine 이 단순 Nat 연산.
- 이 case 에서 combine (u)(v) = u × v 같은 건 fold-structured
  이지만 factoring 을 안 받음 (정보 손실).  분석 필요.

## §4. 잠정 결론

**Lens kernel 공간 cardinality 는 open conjecture**.

가장 그럴듯한 추측:
- Lower: ℵ₀ 확정.
- Upper: 𝔠 확정.
- 실제 값: **countable** (ℵ₀) 일 가능성이 높음 — "fold
  structure 가 충분히 제약적이어서 countable data 만 허용"
  의 직관.  증명은 open.

## §5. 왜 이게 중요한가

이 cardinality 는 **"Raw 가 얼마나 많은 distinct 관측 방식
을 허용하는가"** 의 양적 측정.

만약 countable → **관측 공간이 계산 가능 수준**.  각 관측
방식을 finite algorithm 으로 기술 가능.  수학의 기본 "algebraic"
관측만 허용하는 셈.

만약 𝔠 → **관측 공간이 전체 연속체 크기**.  대부분의 관측은
non-algorithmic, 임의의 choice 를 포함.  공리적으로 더 풍부.

이 선택이 "Raw 가 수학을 가능하게 하는 최소 구조" 의 정체성에
직접 영향.

## §6. 다음

Cardinality 해결은 heavy number theory / universal algebra
작업 필요.  이 arc 에서는 bounds 만 확보하고 conjecture
open.  미래 작업.

Q37.3 (Quotient Lens) 으로 전환.  Cardinality 없이도
constructive 가능.

## 변경 이력

- 2026-04-24: cardinality bounds 정리, 양 방향 후보 argument,
  open conjecture 확립.  Q37.3 로 전환 결정.
