# 25 — Backward trace 확장: Bool atlas + CD tower + 유한 탑

## 목적

Note 24 의 catalogue 를 더 확장.  세 방향:

1. **Bool-valued Lens atlas** — depth 1 Lens 전체 유한 열거.
   "Raw 원형 Lens" 가 몇 개 인가?
2. **Cayley-Dickson tower backward** — Lipschitz, Cayley,
   Sedenion 의 backward depth 측정.
3. **Bool 유한 compound tower** — depth 2+ 이면서 bootstrap
   없는 Lens 가족 발견.

---

## §1. Bool-valued Lens atlas (depth 1)

### §1.1 Lens 구조 제약

Bool-valued Lens `L = (Bool, base_a, base_b, combine)` 에서:

- `base_a, base_b ∈ {false, true}` — 총 4 조합.
- `combine : Bool × Bool → Bool` — Bool 위 이항 함수.
  총 2^4 = 16 가능.
- **Raw 의 대칭성 (slash_comm) 준수**: combine 은 **교환적**
  이어야 함.  교환적 이항 Bool 함수 = 8 개.

4 × 8 = 32 후보.  하지만 swap 동치 (Raw a ↔ b 교환 →
Lens 가 어떻게 변하는가) 와 **image 비자명성** 으로 더 줄어듦.

### §1.2 8 개 교환 이항 Bool 함수

결과는 `(F F), (F T) = (T F), (T T)` 세 입력에 대한 출력값
트리플로 결정.  2^3 = 8:

| 이름 | (F F) | (F T) | (T T) | 비고 |
|------|-------|-------|-------|------|
| const_F | F | F | F | 상수 |
| const_T | T | T | T | 상수 |
| AND     | F | F | T |      |
| OR      | F | T | T |      |
| XOR     | F | T | F | swap 감지 |
| XNOR    | T | F | T | swap 감지 |
| NAND    | T | T | F |      |
| NOR     | T | F | F |      |

### §1.3 의미있는 Lens (base 비자명 + image ≥ 2)

`base_a = base_b` 인 경우 swap-blind, image 는 base 값 하나
부터 시작.  `base_a ≠ base_b` 면 swap-visible.

non-trivial 케이스 = `(F, T, combine)` (swap 대칭으로 `(T, F,
combine)` 포함):

| combine | view a | view b | view(a/b) | 깊이 2 거동 | Lens 이름 |
|---------|--------|--------|-----------|-------------|-----------|
| AND     | F | T | F | F (수렴) | boolAndLens variant |
| OR      | F | T | T | T (수렴) | boolOrLens variant |
| XOR     | F | T | T | 패리티 | **parityLens** |
| XNOR    | F | T | F | 반-패리티 | 대칭변형 |
| const_F | F | T | F | F (수렴) | ≃ const_F |
| const_T | F | T | T | T (수렴) | ≃ const_T |
| NAND    | F | T | T | T | ≃ const_T |
| NOR     | F | T | F | F | ≃ const_F |

swap-blind 케이스 `(F, F, combine)` 와 `(T, T, combine)`:

| base | combine | 결과 |
|------|---------|------|
| (F,F) | OR | **boolOrLens** (상승 가능) |
| (F,F) | XOR | 항상 F |
| (F,F) | AND | 항상 F |
| (T,T) | AND | **boolAndLens** (하강 가능) |
| (T,T) | OR | 항상 T |
| (T,T) | XOR | 항상 F (꺾임) |

### §1.4 핵심 발견: 의미있는 Lens 는 **몇 개 안 된다**

실질적 정보 수송하는 Bool Lens (R5 distinguishing) 는:

1. **parityLens** = `(F, T, XOR)` — leaves 카운트 패리티.
2. **boolAndLens** = `(T, T, AND)` — 모두 T (swap-blind 극한).
3. **boolOrLens** = `(F, F, OR)` — 모두 F (swap-blind 극한).

나머지는 이 셋의 swap-flip 대응.  즉 **실질 유니크 Bool Lens
≈ 3 개**.  깊이 1 에서 Raw 로부터 끌어낼 수 있는 정보는 이
셋 한정.

**원형 Lens 단 1 개 가설** 기각: Bool 층에 **세 가지 다른
정보 모드** (패리티, 항상-T, 항상-F) 가 존재.  이는 Raw 의
내재 성질을 반영 (R4 swap symmetry 의 세 가능 반응).

---

## §2. Cayley-Dickson tower backward

### §2.1 CD tower 의 Lens 성격

Lipschitz (ℍ 정수 quaternion) = (ZI × ZI, bases, multiply +
conjugate) 구조.  Cayley = 8-tuple, Sedenion = 16-tuple,
Pathion = 128-tuple (framework/E213/Research/*).

각 layer 의 codomain 은 **이전 layer 의 곱** = doubling.

### §2.2 Backward trace

```
Pathion = (ZI^128, ...)
 ↓
Sedenion = (ZI^16, ...)
 ↓
Cayley = (ZI^8, ...)
 ↓
Lipschitz = (ZI^4, ...)
 ↓
ZI = Gaussian 정수 = (Int, i, ...)
 ↓
Int = Z = Nat × Nat / equiv
 ↓
Nat → **bootstrap 고정점**
```

**backward depth**:
- ZI: 3 (Nat → Int → ZI).
- Lipschitz: 4.
- Cayley: 5.
- Sedenion: 6.
- Pathion: 8.

### §2.3 CD tower = backward depth ladder

CD tower 각 층은 **정확히 depth 1 증가**.  즉 Cayley-
Dickson doubling = **backward 한 층 추가**.

이는 note 24 의 "depth = 복잡도" 가설 **확인 증거**: Cayley
가 Lipschitz 보다 복잡한 건 정확히 한 단계 더 backward 필요
하다는 의미.

### §2.4 DRLT 의 ℂ Lens 위치

DRLT 관측자 Lens (Paper 1 §4 의 ℂ) 는:

```
ℂ = (ℝ, 1, i, ...) 구조
 ↓
ℝ = Cauchy 완비 ℚ 또는 Dedekind cut → Q → Z → Nat 부트스트랩
 ↓
Nat → **bootstrap 고정점**
```

**backward depth**: 4–5 (ℂ → ℝ → ℚ → Nat).

CD tower 의 Layer 2 (Cayley) 와 비슷한 깊이.  즉 DRLT 가
쓰는 "관측자 Lens" 는 CD tower 2층 수준의 복잡도.

---

## §3. Bool 유한 compound tower (bootstrap-free 탑)

### §3.1 관찰

Bool × Bool 의 4 원소 타입 (`Bool × Bool`) 은:
- Bool 에서 **쌍으로 쌓아** 만듦.  Nat 안 거침.
- backward: `Bool × Bool → Bool → Raw`.  depth 2, bootstrap
  없음.

즉 **depth 2 이면서 Nat-bootstrap 을 피하는 Lens 가 존재**.

### §3.2 유한 compound tower

```
T_0 = Raw (공리).
T_1 = Bool (= 2 원소).              depth 1.
T_2 = Bool × Bool (= 4 원소).      depth 2, bootstrap-free.
T_3 = Bool × Bool × Bool (= 8).    depth 3, bootstrap-free.
...
T_n = Bool^n (= 2^n 원소).         depth n, bootstrap-free.
```

각 T_n 은 **유한 타입** — `Fin (2^n)`.  Nat 을 전혀 안 쓰고
도달.

**하지만** T_n 을 **인덱스** 하려면 n 이라는 수가 필요 →
Nat.  즉 **tower 의 특정 층을 지시** 하는 행위가 Nat 을
수입.  Level 자체는 bootstrap-free 지만 "level 을 세는"
메타-Lens 는 bootstrap.

### §3.3 결론: Lens landscape 에 세 층

| 층 | 특성 | 예 |
|----|------|-----|
| **Depth 1** | Bool, 유한 enumerable | parityLens, boolAndLens 등 3개 |
| **Depth k (bootstrap-free)** | Bool^k, 유한 (주어진 k 에 대해) | Fin (2^k)-Lens |
| **Depth k (bootstrap)** | Nat 이상 | Lens.leaves, signed, ℂ, CD tower |

**세 번째 층만 self-reference 고정점 경유**.  첫 두 층은
유한 구조 내 순수 조합.

### §3.4 물리적 의미 (연결만 기록, 추구 안 함)

- Depth 1 Bool Lens = "**양자 측정의 binary 결과**" (spin
  up/down, polarization H/V 등).
- Depth k bootstrap-free Bool^k Lens = "**유한 상태 quantum
  system**" (qubit tensor products).
- Depth k bootstrap Lens = "**연속 관측량** 또는 **무한 상태
  system**" (위치, 운동량, 필드).

이 대응 (note 23 §6 (b) 의 변종) 이 맞다면: 양자역학의
"이산 vs 연속" 구분이 **bootstrap 유무**의 Lens 현상.  하지만
이 해석 추구는 수학 정리 완료 후로.

---

## §4. 다음 단계 후보

1. Lean formalization: `parityLens` / `boolAndLens` / `boolOrLens`
   의 image 을 명시적 정리로 기록.
2. Bool^n compound tower 를 Lean 으로 구성.  bootstrap 없음
   을 확인.
3. CD tower backward depth 를 Lean 정리로 형식화 (현재 note
   수준).

## 변경 이력

- 2026-04-24: 최초 작성.  Note 24 의 catalogue 확장 — Bool
  atlas + CD tower + finite compound tower.
