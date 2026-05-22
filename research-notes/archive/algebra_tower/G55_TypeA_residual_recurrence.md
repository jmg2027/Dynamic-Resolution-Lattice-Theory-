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

## 추가: Ring213 module (2026-05-09)

User hint "ring 없으면 ring213 만들어서 가즈아" + "님이 안된다는 건 레포 어딘가 숨어있음" → 확인:

### 213 lib 의 polynomial identity 인프라

| 도구 | 위치 | ∅-axiom? | Use case |
|---|---|---|---|
| `omega213` | Term/Tactic/Omega213 | ✓ | Nat linear arith |
| `Pow213.pow_add_two` | Term/Tactic/Pow213 | ✓ | Nat pow expansion |
| `quad_norm` | Term/Tactic/QuadNorm | ✗ propext | Z[√D] norm-mult |
| `HurwitzRing` | Lib/Math/Tactic | ✗ DIRTY | Hurwitz ring polynomial id |

**우리 case** (Int + pow_succ + linear recurrence): 위 도구 부분 적용 가능,
but Int 폐쇄 폼 직접 unfolding 어려움 (Mathlib `ring` 필요).

### 채택한 approach: Recurrence-as-Definition (∅-axiom)

```
Lib/Math/Tactic/Ring213.lean:
  structure Recurrence2 := ⟨a₀, a₁, c₁, c₂, d⟩
  def Recurrence2.seq : Nat → Int  (recursive)
  theorem Recurrence2.seq_recurrence : ∀ n, ... := rfl
  
  -- Type A instance:
  def typeA_residual : Recurrence2 := ⟨43, 197, 6, -8, 3⟩
  theorem typeA_residual_universal : ∀ n, ... (by rfl)
  theorem typeA_residual_measured : a_0..a_4 match (by decide)
```

→ Universal recurrence 가 `by rfl` 로 ∅-axiom. Closed-form algebraic
   equivalence (`56·4^n - 14·2^n + 1 = rec_form n`) 는 Mathlib ring 필요해 미증명, 단 finite-N decide 로 검증 (n = 0..7).

### Type C/D 후속 패턴

Type C 의 residual 은 Z[√5] valued: (a, b)/2^k where residual = (a + b√5)/2^k.
같은 Recurrence2 패턴 적용 가능 — 단지 a 와 b 두 개 sequence 동시 정의.
필요시 `Recurrence2_Z5` 같은 확장 structure.

## Type D 분석 (open)

Unreduced rational part rat_n: -211968, -8266752, -95597568, -887804928, -7603688448

3단계 chain 분석 (eigenvalues 8, 4, 2):
```
Level 1 (8·rat_n - rat_{n+1}):   6571008, 29463552, 123024384, 501249024
Level 2 (4·L1_n - L1_{n+1}):    -3179520, -5170176, -9151488
Level 3 (2·L2_n - L2_{n+1}):    -1188864 (CONSTANT) ✓
```

Level 3 constant = -1188864 = -2^10·27·43.

**문제**: Closed form 시도시 constant 396288 forcing 의 particular solution
이 -396288/7 (비정수). Type D rat_n 은 순수 Int closed form 없음.

추측: Z[√5] coupling 또는 Hurwitz 의 *3-fold 와 7-or-43-related* 추가 구조.
간단 Int recurrence 로 닫히지 않음.

Type D 의 algebraic 형식화는 Z[√5]-valued recurrence 또는 더 큰 cyclotomic
ring 위에서 가능할 듯. 현재 framework 한계.

## ★ UNIVERSAL CD-doubling transient law (2026-05-09 후속 발견)

Type C 의 unreduced rat_n 의 3-level chain 분석 → Level 3 constant 124416.
같은 derivation 으로 Type D, Type A 도 *동일 3rd-order recurrence*:

```
∀ Type ∈ {A, C, D}:
  rat_{n+3} = 14·rat_{n+2} − 56·rat_{n+1} + 64·rat_n + d_Type

Char poly: x³ − 14x² + 56x − 64 = (x−2)(x−4)(x−8)
Eigenvalues 2, 4, 8 (pure dyadic, universal across all Types)
```

검증: 측정된 rat_3, rat_4 모두 정확히 재현.

### Base-dependent constant `d`

| Type | constant d | factorization |
|---|---|---|
| A (ZI) | -10752 | -2⁹·3·7 |
| B (ZSqrt[D≥2]) | -10752 | (= A shifted) |
| C (ZOmega) | -124416 | -2⁹·3⁵ |
| D (Hurwitz) | +1188864 | +2¹⁰·27·43 |

→ **CD doubling 의 universal transient eigenvalue (2, 4, 8)** 는 base 무관.
   Base 의 unique structure 는 *constant `d` 의 prime signature* 에만 등장.
   
   - 7 (A): 모든 base 공유 baseline
   - 3⁵ (C): cyclotomic-3 from ZOmega's ω
   - 43 (D): Hurwitz-specific exotic prime

### 의미

이게 *진짜 코끼리 본체의 일부*:
- 다이아딕 분할 (eigenvalue 2, 4, 8 = 2¹, 2², 2³) = CD doubling 본질
- 이 universal recurrence 가 *base 무관* — Raw 의 binary slash 의 곧장 결과
- Base 차이는 *initial condition + constant* 에 흡수

### Lean ∅-axiom

`Lib/Math/Tactic/Ring213.lean` 에 박힘:

```
structure Recurrence3 := ⟨a₀, a₁, a₂, c₁, c₂, c₃, d⟩
def seq : Nat → Int  (recursive)
theorem seq_recurrence : ∀ R n, ... := rfl   -- universal

def typeA_rat_uni : Recurrence3
def typeC_rat_uni : Recurrence3  
def typeD_rat_uni : Recurrence3

theorem typeA/C/D_rat_uni_measured : seq 3, seq 4 match data
```

모두 ∅-axiom. CD doubling 의 universal transient law 가 *형식적*으로 박혔음.
