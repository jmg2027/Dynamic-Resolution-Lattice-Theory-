# G55: Type A 의 transient residual = 닫힌 선형점화식

## Discovery

Type A (D=1, ZI) 의 layer-by-layer Moufang fail rate 가 *exact closed
form*. Pell/Fib 아닌 *순수 dyadic*.

## Data (Type A residuals)

residual_n = 1/2 − rate(L_{n+5}). 분자 (분모 2^(7+3n)):

| n | layer | rate | 분자 a_n |
|---|---|---|---|
| 0 | L5 | 21/128 | **43** |
| 1 | L6 | 315/1024 | **197** |
| 2 | L7 | 3255/8192 | **841** |
| 3 | L8 | 29295/65536 | **3473** |
| 4 | L9 | 248031/524288 | **14113** |

## Recurrence

```
a_{n+2} = 6·a_{n+1} − 8·a_n + 3
```

검증:
- a_2 = 6·197 − 8·43 + 3 = 841 ✓
- a_3 = 6·841 − 8·197 + 3 = 3473 ✓
- a_4 = 6·3473 − 8·841 + 3 = 14113 ✓

특성: x² − 6x + 8 = (x−2)(x−4). Eigenvalues **2, 4**.

## Closed form

```
a_n = 56·4ⁿ − 14·2ⁿ + 1
```

검증: a_0 = 43, a_4 = 14113 모두 ✓

## 의미

Type A 의 모든 layer rate 가 *exact*:
```
rate(L_{n+5}) = 1/2 − (56·4ⁿ − 14·2ⁿ + 1) / 2^(3n+7)
```

→ 무리수 없이 정수표현. eigenvalue 2, 4 = 2¹, 2² (pure dyadic).

## Type A vs C/D

Type A asymptote = 1/2 (rank 0) → φ 안 등장 자연. eigenvalue 2-power.

Type C/D asymptote ∈ Z[√5] → residual recurrence 에 √5 들어와야.
*Z[√5]-valued* recurrence 미발견 (open).

## Lean ∅-axiom 후보

```
def typeA_residual_num : Nat → Int
  | 0 => 43
  | (n+1) => 4 * typeA_residual_num n + 28 * 2^n - 3   -- not yet, need 2-step

-- 2nd order linear:
theorem typeA_residual_recurrence (n : Nat) :
    closed_form (n+2) = 6 * closed_form (n+1) - 8 * closed_form n + 3
  where closed_form (k : Nat) : Int := 56 * 4^k - 14 * 2^k + 1
```

이건 Nat/Int 산술이라 ∅-axiom decide 가능.

## 다음

1. Lean 에 typeA closed form ∅-axiom 정리화
2. Type C, D residual 을 Z[√5] 위에서 시도
3. arbitrary base 의 residual recurrence form 일반 추출
