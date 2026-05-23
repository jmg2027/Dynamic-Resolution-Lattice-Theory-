# G62: ℕ → ℤ as orthogonal-axis transition + lost properties

## User's reframing (2026-05-09)

> "수직선의 양끝단이 아니라 직교하는 좌표로.  아마 213에선 그게 더
> 자연스러울거여."

ℕ → ℤ을 "1D 직선의 양방향 확장"으로 보지 말고, **두 직교축의
quotient projection**으로 보자.

> "그리고 P의 (2x+1)/(x+1) 자체가 213의 동적인 모습인거 같아서
> 맞는 방향인가는 좀 의문이긴 하네."

P는 dynamic 측면.  Static tower의 driver는 다른 것일 수 있음.
P를 일단 보류하고 axis-구조 자체로 진행.

> "자연수가 정수가 되면서 잃어버린 성질이 있을것이여."

전환 시 잃는 것을 명시적으로 catalog.

## 직교 좌표 framing

### 1D 양끝단 view (지금까지)
```
        |---0----1----2----3---->     ℕ (한쪽 직선)
<--(-3)-(-2)-(-1)-0----1----2----3-->  ℤ (양쪽 직선)
```
"L0→L1 = 음수 추가" — 1D 라인이 양방향으로 확장.

### 직교축 view (새 framing)
```
ℕ × ℕ                ℤ
^                    ^
|. . . .             |    -1   1
|. . . .   ─────→    |---------------→
|. . . .             |   -2 -1 0 1 2
|. . . .             v
+-----→
ℕ
```

ℤ = `ℕ × ℕ / ~` where `(a, b) ~ (c, d) ⟺ a + d = b + c`.

각 정수 `n`은 **두 직교 자연수의 차**로 표현:
- `(a, b)` represents `a - b`
- 같은 정수의 여러 representation: `2 = (2,0) = (3,1) = (4,2) = ...`
- equivalence class = **diagonal-translation orbit**

### 213-naturalness

이 framing이 213-native인 이유:
- 213은 **NS=3, NT=2** 두 직교축 base
- ℕ 두 카피 (`a` axis와 `b` axis)는 자연스럽게 NS-axis와 NT-axis 같은
  관계
- "양방향 직선" framing은 음수를 외부에서 가져오는 느낌이지만,
  "직교축" framing은 두 같은-방향 자연수의 비교/차이만 사용
- `Raw/Signed.lean`의 `swap`은 이 (a, b) → (b, a) 교환을 정확히
  realize함 (그리고 fold에서 negation으로 됨)

## ℕ → ℤ에서 잃는 성질들

### A. Order-theoretic 손실

| 성질 | ℕ에서 | ℤ에서 |
|---|---|---|
| **Well-ordering** | 모든 nonempty subset에 min | 음의 무한 강하 가능, no min |
| **존재 minimum** | 0 = least element | 없음 |
| **Bounded below** | 0 ≤ n ∀n | 없음 |
| **Strong induction** | 표준 ℕ-induction | 양방향 weak induction만 |
| **Order-multiplicative** | a ≤ b → a·c ≤ b·c (∀c ≥ 0) | c < 0 시 역전 |

**가장 fundamental 손실 = well-ordering.**  ℤ는 well-ordered 아님.

### B. Algebraic 손실

| 성질 | ℕ에서 | ℤ에서 |
|---|---|---|
| **Free commutative monoid on 1 generator** | ℕ ≅ Free CMon({⋆}) | 아님 |
| **Universal property to CMonoid** | unique hom ℕ → 모든 CMonoid | only Groups에 unique hom |
| **Atomic uniqueness** | n = ⋆+⋆+...+⋆ unique | n = many ways = (a) - (b) |

**가장 deep 손실 = "atom으로의 unique representation"**.

ℕ에서 `3 = 1+1+1` (atom 3개) — 단일.
ℤ에서 `3 = (3, 0) = (4, 1) = (5, 2) = ...` — equivalence class.

이게 **representation degeneracy**: 같은 정수에 여러 atomic
representation 가능.  ℕ→ℤ 전환은 **atomic-uniqueness를 quotient
class로 collapse하는 것**.

### C. 구조적 (asymmetric) 손실

| 성질 | ℕ에서 | ℤ에서 |
|---|---|---|
| **Successor-Predecessor asymmetry** | succ 항상 정의, pred(0)은 undef | 둘 다 항상 정의 |
| **0 as "wall"** | 한 방향 wall | wall 없음 |
| **Atom-direction** | + 방향 unique | ± 양쪽 대칭 |
| **Counting semantic** | 사물 수 직접 표현 | "−3 사과" 비물리 |

**가장 213-flavor 손실 = succ-pred asymmetry**.

ℕ의 비대칭성은 **Raw의 atom-axis 비대칭성**과 isomorphic.  ℤ로 가면
Raw의 swap-symmetric 구조가 enforce됨 — 즉 ℤ는 **swap-quotient의
materialization**.

### D. Topological / 측도 손실

| 성질 | ℕ에서 | ℤ에서 |
|---|---|---|
| **One-sided density** | density at +∞ only | density at ±∞ both |
| **Half-line topology** | 0 boundary | no boundary |
| **Asymptotic counting** | n/log(n) prime density | 같은 상수, 양방향 |

이건 약한 손실 (대부분 보존).

### E. Categorical 손실

ℕ과 ℤ의 categorical 위치:

```
              Forget structure
ℤ (group) ────────────────→ ℕ (monoid)
   ↓                            ↓
   ↓                            ↓
   Inverse-adjunction:    Grothendieck:
   add inverses           free group on
   gives ℤ                ℕ-as-monoid
```

**Forgetful functor**가 ℤ→ℕ에 **존재하지 않음** — ℕ은 ℤ의 sub-monoid이지만,
ℤ에서 자연스러운 "ℕ 부분" 추출은 order-dependent.  즉 **ℤ→ℕ
canonical retraction 없음**.

이게 categorical 손실: **information loss at the structure-level**.
Forgetting inverse 후 unique sub-monoid 결정 못 함.

## 직교축 view에서의 손실 재해석

ℕ²로 가면:
- **ℕ²은 ℕ의 모든 성질 유지** (well-ordering도 product order로 유지)
- **ℕ² → ℤ projection**에서 진짜 잃는 것 = **fiber 정보**
  - 정수 `n`의 representation `(a, b)` = `(n+k, k)` for ∀k ≥ 0
  - 즉 각 정수가 **무한 fiber** (1차원 ray)를 가짐
  - Projection ℕ² → ℤ는 **diagonal-translation orbit으로 collapse**
  - **잃는 것 = "어느 representative인가" 정보**

이 "fiber 정보 손실"이 다른 view들의 통합:
- representation degeneracy = fiber에 무한 many points
- well-ordering 손실 = fiber direction이 unbounded
- atomic uniqueness 손실 = 같은 정수 = 다른 atom-pair
- swap-symmetry 발현 = (a,b) ↔ (b,a) = +n ↔ -n

## 그래서 "2-쪽 확장"의 정확한 의미

직교축 framing에서:

> **ℕ → ℤ는 1축 → 2축 + diagonal-quotient**

"2-쪽" = 두 직교 ℕ-축이 들어옴.  Quotient는 둘을 1차원으로
projection (둘의 차).

**손실** = 두 축의 독립 정보 (fiber).

**얻음** = 음수 (= 어느 axis가 더 큰지의 부호).

이 framing에서 **3-쪽 확장**은 자연스럽게:

> **3 직교 ℕ-축 (ℕ³) + 어떤 quotient**

가장 단순한 quotient: total-diagonal `(a,b,c) ~ (a+k, b+k, c+k)`
→ result는 ℤ²-like (2D signed).

또는 **3개 사이의 cyclic 비교** = `(a,b,c) ~ (b,c,a)` (cyclic shift) +
diagonal translation → 결과는 ℤ²/Z₃ 같은 것.

이게 진짜 "3-쪽 확장"의 후보.  자세한 건 아래.

## 3-axis 확장 시도 (orthogonal framing 기반)

ℕ³ + quotient 후보들:

### 후보 (i): Total diagonal
```
ℕ³ / ((a,b,c) ~ (a+k, b+k, c+k))
```
- 2D signed lattice (ℤ²-like)
- canonical reps: `(a, b, c)` with min coord = 0
- 사실상 "ℤ²" — 3-fold이지만 effective dim = 2

### 후보 (ii): Two-axis paired diagonal
```
ℕ³ / ((a,b,c) ~ (a+k, b+k, c)) -- 첫 두 축만 quotient
```
- ℤ × ℕ — 한 축은 signed (= 차이), 한 축은 자연수 그대로
- 비대칭 mixed structure

### 후보 (iii): Cyclic shift quotient
```
ℕ³ / Z₃ where (a,b,c) ~ (b,c,a) ~ (c,a,b)
```
- multiset of 3 naturals (unordered)
- 차원 = 2 (representative `(a,b,c)` with `a ≤ b ≤ c`)
- **3-fold cyclic symmetry built in**

### 후보 (iv): Cyclic + diagonal
```
ℕ³ / (Z₃ ∪ diagonal-translation)
```
- 가장 풍부한 quotient
- result ≅ ?  — possibly ℤ²/Z₃ or "Eisenstein-like ℤ[ω]"!

이게 **3-axis 확장이 ZOmega와 연결되는 path**일 수 있음.

검증:
- `ℤ[ω]`의 representation: `a + b·ω`, `a, b ∈ ℤ`
- ω = e^(2πi/3) = cube root of unity
- ℤ[ω] = 2D lattice with **3-fold rotational symmetry**
- **Z₃ acts by ω-multiplication**

후보 (iv)는 **lattice ℤ²에 Z₃ rotation을 quotient한 것**과
구조적으로 일치!  ℤ[ω]는 ℤ² lattice의 specific embedding, 그리고
Z₃ rotation이 자연스러움.

## 잠정 결론 + 다음 step

**ℕ → ℤ 직교축 reframing의 의의**:
1. "음수 추가" view보다 213-naturalness가 명확
2. 잃는 성질 catalog가 더 깔끔 (fiber 정보 손실로 일관)
3. 3-axis 확장에서 **Z₃ symmetry가 자연스럽게 등장** → ZOmega
   (Eisenstein) 설명력

**P-driver vs static structure 분리**:
- P는 dynamic iteration (Pell-Fib)
- Static tower는 axis-orthogonality + quotient의 chain
- 두 분리해서 다루는 게 맞음

**다음 candidates**:
(a) 후보 (iv) = ℕ³ / (Z₃ + diagonal)이 정확히 ℤ[ω]인지 ∅-axiom 형식화
(b) "lost properties" Lean 형식화 (well-ordering on ℕ vs not on ℤ)
(c) ℕ² / diagonal ≅ ℤ ∅-axiom 형식화 (Grothendieck completion)
(d) Layer growth: 1-axis → 2-axis → 3-axis → ... 의 unit count law
(e) 좀 더 후보 탐색 (k-axis general framework)

## See also

- `lean/E213/Theory/Raw/Signed.lean` — swap-as-negation (1↔2축
  교환의 fold 결과)
- `lean/E213/Theory/Internal/Int213.lean` — ℤ in 213-native form
- `research-notes/G61_213_tower_research_candidates.md` — 광범위
  candidate list
- `research-notes/G29_residue.md` — pointing-residue, atomic
  asymmetry
