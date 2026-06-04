# G140 — P가 모든 자연수를 생성한다

**Date**: 2026-05-26
**Status**: CLOSED (Lean formalised, refined)
**Lean**: `E213.Lib.Math.Mobius213.Px.PGeneratesNat`

## 핵심 관찰

> "모든 자연수들을 P 자체로 생성하는 이론을 만들어보자
>  (7 같은 수도 다 만들 수 있음)"

뫼비우스 행렬 P = [[2,1],[1,1]]로부터:
- det(P) = 1
- P₁₁ = NT = 2
- tr(P) = NS = 3

gcd(2, 3) = 1이므로, **Chicken McNugget 정리** (= Sylvester-Frobenius):
> (2, 3)의 Frobenius 수 = 2·3 − 2 − 3 = **1**

따라서 **모든 n ≥ 2는 2a + 3b (a,b ≥ 0)로 표현 가능**.
1 = det(P)와 합치면:

> **∀ n ≥ 1, n은 P-생성.**

## 이전 "자연성 경계"와의 비교

| 닫힘 방식 | 집합 | 빠지는 수 |
|---|---|---|
| 곱셈만 {1,2,3,5}^× | {1,2,3,4,5,6,8,9,10,12,15,...} | 7, 11, 13, 14, ... |
| 덧셈 {2,3}^+ | {2,3,4,5,6,7,8,...} = ℕ≥2 | 없음 (≥2 전부) |
| P-생성 (det∪덧셈) | ℕ \ {0} | **없음** |

"7 ∉ atomic closure" 문제는 곱셈만 고려한 인위적 제한이었다.
행렬 P 자체는 덧셈도 허용하므로, 모든 자연수를 생성한다.

## 수학적 구조

### 증명 (강한 귀납법)
- Base: n=2 → NT, n=3 → NS
- Step: n ≥ 4 → (n−2) ≥ 2이므로 IH 적용, NT를 더함

### 깊이 이론 (minDepth)
P-덧셈 깊이 = min{a+b : 2a+3b = n}.  Greedy mod-3 공식:
- n ≡ 0 mod 3 → depth = n/3
- n ≡ 1 mod 3 → depth = (n−4)/3 + 2
- n ≡ 2 mod 3 → depth = (n−2)/3 + 1

| n | depth | 분해 |
|---|---|---|
| 2 | 1 | 2·1 + 3·0 |
| 3 | 1 | 2·0 + 3·1 |
| 7 | 3 | 2·2 + 3·1 |
| 11 | 4 | 2·1 + 3·3 |
| 13 | 5 | 2·2 + 3·3 |
| 97 | 33 | 2·2 + 3·31 |
| 100 | 34 | 2·2 + 3·32 |

**최적성 증명**: `minDepth_optimal` — 어떤 분해 n=2a+3b에 대해서도
a+b ≥ minDepth n.  Greedy (3을 최대한 사용)가 최적.

### 왜 P가 ℕ를 생성하는가 (필연성)
1. P = Q² (Q = Fibonacci shift [[1,1],[1,0]])
2. 연속 Fibonacci 수는 항상 서로소: gcd(Fₙ, Fₙ₊₁) = 1
3. P의 trace와 entry: gcd(NS, NT) = gcd(F₄+F₂, F₃) = gcd(3,2) = 1
4. Frobenius 정리 → 1보다 큰 모든 수가 2a+3b로 표현

∴ P의 Fibonacci 구조가 보편 생성을 **강제**한다.

### 정확한 특성화 (§8)
```
PGen n ↔ n ≥ 1
```
- `not_pgen_zero`: 0은 P-생성 불가
- `pgen_pos`: PGen n → n ≥ 1
- `pgen_iff_pos`: **동치** — P-생성 = 양의 자연수

### 반환 구조 (Semiring)
PGen은 sub-semiring:
- 1 ∈ PGen (단위원)
- a, b ∈ PGen → a+b ∈ PGen (덧셈 닫힘)
- a, b ∈ PGen → a·b ∈ PGen (곱셈 닫힘)

## 형식화 현황 (9개 절, ~40 선언)

| 정리 | 내용 |
|---|---|
| `PGen` | P-생성 귀납적 술어 (5-constructor) |
| `chicken_mcnugget_23` | ∀ n≥2, ∃ a b, n=2a+3b |
| `pgen_ge_two` | ∀ n≥2, PGen n |
| `pgen_all_pos` | ∀ n≥1, PGen n |
| `not_pgen_zero` | ¬ PGen 0 |
| `pgen_pos` | PGen n → n ≥ 1 |
| `pgen_iff_pos` | ★ PGen n ↔ n ≥ 1 (동치) |
| `pgen_semiring_closure` | 반환 닫힘 3-절 |
| `p_generates_nat_master` | 5-절 마스터 |
| `minDepth` | 최소 P-덧셈 깊이 함수 |
| `minDepth_optimal` | 최적성: minDepth ≤ a+b |
| `coprime_NS_NT` | gcd(3,2) = 1 |
| `frobenius_NT_NS` | 2·3−2−3 = 1 |
| `prime_rep23_witnesses` | 소수 ≤ 47 전부 Rep23 증인 |

**∅-axiom 준수**: 0 sorry, 0 native_decide, 0 Mathlib, 0 Classical.

## 의의

1. **자연성 경계 폐기**: "7은 비원자적" → 무의미. P가 7을 2+2+3으로 즉시 생성.
2. **P-궤도 링 = ℤ 전체**: L(0)=2, L(1)=3, gcd=1 → 덧셈으로 ℤ 전체 도달.
3. **보편 생성자**: P는 단순히 조합론/정수론의 구조 상수가 아니라,
   **자연수 전체의 가산적 생성자**.
4. **정확한 특성화**: PGen n ↔ n ≥ 1.  P-생성의 경계는 0뿐.
5. **깊이가 유일한 불변량**: n이 P-생성인지는 자명 (항상 yes for n≥1).
   남는 구조적 정보는 **깊이** = 최소 P-항 합 개수뿐.
6. **최적성**: greedy mod-3 전략이 최적임을 증명 (`minDepth_optimal`).

## 한 문장 요약

> 뫼비우스 행렬 P = [[2,1],[1,1]]은 det=1과 gcd(tr, entry) = gcd(3,2) = 1을
> 동시에 만족하므로, 모든 양의 자연수를 그 원소의 유한 덧셈만으로 생성한다.
> 정확히: **PGen n ↔ n ≥ 1**.  "원자적 곱셈 닫힘"을 넘어 "P-덧셈 보편성"이
> 참된 자연성 경계이다.
