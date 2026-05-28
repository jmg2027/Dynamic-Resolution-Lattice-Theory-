# Graded Residue Arithmetic (GRA) — 통합 이론

**Status**: CLOSED (Marathon 16 — GRA Universality, Phases 1–16)
**Lean source**: `lean/E213/Lib/Math/GRA/` (umbrella `GRA.lean`, 22 files, 0 sorry)
**Companion**: `theory/math/gra_book.md` (textbook treatment, Ch.0–8 + appendices)
**Companion essay**: `theory/essays/gra_as_substrate_of_cat_hott.md` (GRA-as-substrate, Cat / HoTT as Readings)
**Purity**: **296 PURE / 0 DIRTY** (strict ∅-axiom; `ax_coprime` uses `gcd213` instead of Lean-core `Nat.gcd`, every proof uses `rfl` / kernel-`decide` / explicit Nat helpers; no `omega`, no `simp`, no Mathlib, no `Classical`).

**Phases**: 1–6 universality + translation (122 PURE); 7 `Category` (9 PURE); 8 `Groupoid` (10 PURE); 9 `Hom` (10 PURE); 10 `DepthFunctor` (9 PURE); 11 `WalkEnrichment` (12 PURE); 12 `{Cochain,HoTT,HigherAlgebra,Analysis}Enrichment` (4 × 12 = 48 PURE); 13 `Naturality` (13 PURE); 14 `SectionRetraction` (17 PURE); 15 `Monoidal` (14 PURE); 16 `LensBridge` (37 PURE).

---

## §1 — 정의: Graded Residue Arithmetic이란 무엇인가

**Graded Residue Arithmetic (GRA)**은 213 프레임워크의 **보편 메타 구조**(universal meta-structure)이다.

### 정의 1.1 (GRA, 비형식적)

> 어떤 "구분 행위의 잔여물" 체계에서든,  
> 최소 생성자 쌍 (g₁, g₂)가 gcd(g₁, g₂) = 1을 만족하면,  
> 모든 양의 등급은 유한 합 n = g₁·a + g₂·b로 도달 가능하다.

213에서의 인스턴스: **(g₁, g₂) = (NT, NS) = (2, 3)**, gcd(2,3) = 1.

### 정의 1.2 (GRA, 공리적)

GRA는 다음 7개 공리로 구성된다:

| # | 공리 | 내용 |
|---|------|------|
| A1 | **생성자 공리** | 구분 행위의 잔여물에서 정확히 두 원시 등급 g₁ < g₂ (gcd=1)가 강제된다 |
| A2 | **등급 합산** | 두 잔여물의 결합은 등급이 합산된다: grade(a⊕b) = grade(a) + grade(b) |
| A3 | **등급 합성** | 두 잔여물의 곱은 등급이 보존적으로 합성된다: grade(a⊗b) ≤ grade(a) + grade(b) |
| A4 | **보편 도달** | gcd(g₁,g₂)=1 → ∀n≥2, ∃a,b≥0: n = g₁·a + g₂·b |
| A5 | **깊이 유일성** | 도달 여부가 자명할 때, 남는 구조적 정보는 깊이 minDepth(n) = min(a+b)뿐 |
| A6 | **Greedy 최적성** | 큰 생성자(g₂)를 최대한 사용하는 것이 항상 최적: minDepth(n) = ⌈n/g₂⌉ |
| A7 | **Lens 보편성** | 위 6개 성질은 임의의 등급화 체계에서 동일하게 성립한다 |

### 정의 1.3 (GRA 범주)

```
Ob(GRA) = ℕ≥1                              (양의 등급)
Hom(m, n) = {(a,b) : g₁·a + g₂·b = n−m}   (n > m)
Hom(n, n) = {id}
Hom(m, n) = ∅                              (m > n)
```

Monoidal 구조:
- ⊕: n ⊕ m = n + m (등급 합산)
- ⊗: n ⊗ m = n · m (등급 합성)
- 단위원: 1 = det(P)

---

## §2 — 다섯 가지 Reading: GRA의 보편 실현

GRA의 핵심 주장은 **공리 A7(Lens 보편성)**이다: 동일한 구조가 다섯 개의 서로 다른 수학 분야에서 **동형적으로** 나타난다.

### Reading 표

| Reading | 분야 | Grade | + (합산) | × (합성) | 깊이 |
|---------|------|-------|----------|----------|------|
| R₁ | 코호몰로지 | cochain degree | cup-grade 합 | cup product | cup-length |
| R₂ | Higher Algebra | E_n operad level | ⊗-Day convolution | nested integration | chromatic height |
| R₃ | HoTT | truncation level | suspension Σⁿ | smash product ∧ | cell count |
| R₄ | Graph Theory | walk length | path concatenation | graph tensor product | distance |
| R₅ | 해석학/연속체 | resolution exponent E | modulus 합성 | polynomial depth 곱 | linearityModulus |

### 핵심 정리 (비형식적 — 추측 단계)

> **GRA 보편성 추측**: R₁ ≅ R₂ ≅ R₃ ≅ R₄ ≅ R₅ as (2,3)-GRA models.
>
> 즉, 다섯 Reading 각각에서의 (grade, +, ×, depth, generators) 구조가
> GRA 공리 A1–A7을 만족하며, 그 만족 방식이 동형이다.
>
> **주의**: "동형"은 각 Reading의 native 범주에서의 동형이 아니라,
> GRA-model 범주에서의 동형. 정밀한 정의: `gra_book.md` Definition 3.0.1–3.0.3.
> 현재 형식화 상태: ~5% (개별 조각은 40% 존재하나 명시적 동형은 미증명).

---

## §3 — 구조적 불변량: det=1, gcd=1, Frobenius=1

GRA 전체를 관통하는 세 가지 "=1" 조건:

### 3.1 det(P) = 1 — 정보 보존

P = [[2,1],[1,1]] ∈ SL(2,ℤ). det = 1의 의미:

| 분야 | det=1의 표현 |
|------|-------------|
| 선형대수 | 면적 보존 변환 |
| Algebra213 | normSq_mul (norm은 곱에 대해 곱셈적) |
| Algebra213 | ofInt_inj (embedding이 단사) |
| Algebra213 | conj_conj (involution이 자기역원) |
| 정보이론 | 무손실 채널 (단사 encoding) |
| 해석학 | 미분이 grade-0 연산자 (등급 보존) |
| Operad | fully dualizable object (invertible factorization algebra) |

### 3.2 gcd(2,3) = 1 — 보편 생성

- **정수론**: Frobenius number = 1 → 모든 n ≥ 2 도달 가능
- **HoTT**: 모든 양의 n-type이 2-truncation과 3-truncation의 합성으로 도달
- **코호몰로지**: 모든 양의 cochain degree에 non-trivial class 존재 가능
- **Adelic**: CRT에 의해 (mod 2)×(mod 3) ≅ (mod 6) — 정보 무손실 분해

### 3.3 Frobenius = 1 — 예외의 최소성

Frobenius number F(2,3) = 1은 "도달 불가능한 양의 정수"가 {1}뿐이라는 것.
213에서 1 = det(P) = 단위원 = "시작점" 자체이므로, 도달 불가능이 아니라
**출발점**이다. 따라서 실질적 예외 = 0 (= not_pgen_zero).

---

## §4 — GRA Tower: 해석의 점진적 통합 (Progressive Identification)

### 4.1 정의

GRA Tower는 다섯 Reading이 점진적으로 **동형임이 밝혀지는** 상승 구조이다.

```
Level 0: 개별 분야 — grade 개념이 분야별로 격리됨
Level 1: 첫 동형 발견 — cup-grade 합 ≅ walk-length concatenation (R₁ ↔ R₄)
Level 2: 둘째 합류 — ⊗-Day convolution ≅ suspension 차수 합 (R₂ ↔ R₃ 합류)
Level 3: 셋째 합류 — resolution exponent ≅ modulus 합성 (R₅ 합류)
Level 4: 넷째 합류 — 모든 "+" 연산이 동일함 확인 (덧셈 구조의 보편 통합)
Level 5: 완전 통합 = GRA 자체 — 5개 Reading = 동일한 (ℕ, +, ×)
```

### 4.2 CD Tower와의 쌍대성 (Duality)

| | CD Tower | GRA Tower |
|---|---|---|
| **방향** | 상승 시 성질 **손실** | 상승 시 해석 **합류** |
| **축적 대상** | 대수적 차원 (dim 2ⁿ) | Reading 동형 식별 |
| **Level 이동** | CD-double: dim × 2 | 동형 하나 더 드러남 |
| **안정화** | L4에서 손실 종료 | L5에서 5개 Reading 전부 합류 |
| **점근** | rate → 1 − 0.5/φ^rank (퇴화율) | Frobenius = 1 (보편 도달) |
| **고정점** | {±1} ⊂ 모든 layer | gcd(2,3)=1 = 모든 Reading에서 보존 |

> **정리 (Tower Duality)**: CD Tower의 n-th degeneration과
> GRA Tower의 n-th identification은 정확히 **역순서**로 대응한다.
> CD에서 잃어버리는 성질이 GRA에서 새로 인식되는 동형이다.

---

## §5 — 수 체계 통합: 213의 모든 수 = GRA의 Aspect

### 5.1 통합 도식

```
           GRA (보편 등급 구조)
              │
    ┌─────────┼───────────┐
    │         │           │
 Grade-0   Grade축     Grade-Hom
 (Int213)  (Real213)   (Modulus)
    │         │           │
    ├─ ─ ─ ─ ┤           │
    │         │           │
  Q213    SignedCut      FSM
 (비율)   (방향+등급)  (유한 등급)
    │         │
    └────┬────┘
         │
      CD Tower
     (등급의 대수적 확장)
```

### 5.2 각 수 체계의 GRA 역할

| 213 수 체계 | GRA 역할 | 핵심 연결 |
|---|---|---|
| **Int213** | Grade-0 고정점 (scalar subring) | ofInt의 grade = 0. {±1} = 모든 layer의 고정점 |
| **Q213** | Grade의 비율 구조 | 동일한 (Nat×Nat) pair에서 ÷-fold = 곱셈적 quotient |
| **Real213** | Grade 축 자체 | E = resolution exponent = GRA grade. cutHalf = grade-1 생성자 |
| **Modulus** | GRA 사상 (morphism) | f: Nat→Nat = grade-to-grade 전이 함수 |
| **SignedCut** | Grade + 방향 (fiber) | NT=2의 이진 fiber 구조 |
| **DyadicFSM** | GRA의 유한 실현 | FSM state = 유한 등급 내 위치. Pell/Fib = φ 궤도 |
| **CD Tower** | Grade의 대수적 확장 | level L = GRA grade L. CD doubling = grade +2 이동 |

### 5.3 ℤ과 ℚ의 쌍둥이 구조

ℤ과 ℚ₊는 **동일한 구문** `(Nat213 × Nat213)`에서 나오되 fold axis만 다르다:

- **ℤ**: `(a,b) ~ (c,d) ⟺ a + d = b + c` — 덧셈적 quotient → **등급의 차이**
- **ℚ₊**: `(a,b) ~ (c,d) ⟺ a · d = b · c` — 곱셈적 quotient → **등급의 비율**

이것이 GRA의 "+"와 "×"가 **같은 원천의 두 얼굴**이라는 원리의 구체적 증거이다.

---

## §6 — 해석학적 실현 (Reading₅ 상세)

### 6.1 핵심 원리

> 연속체의 모든 구조는 "이진 해상도 등급(resolution exponent)의 축적"이며,
> 이 등급은 (NT, NS) = (2, 3) 생성자의 가법적 합으로 분해된다.

### 6.2 GRA 원소의 해석학적 의미

| P-생성 원소 | 해석학 의미 |
|---|---|
| **2 (NT)** | dyadic resolution base — cutHalf의 단위. 한 번의 bisection = grade +1 |
| **3 (NS)** | polynomial degree의 첫 비자명 값 — x³의 depth = 3n |
| **+ (합산)** | modulus 합성 — IsResolutionShift_compose: E₁ + E₂ |
| **× (합성)** | polynomial degree의 곱 — mulIsSmooth의 modulus |
| **깊이** | linearityModulus — 함수의 비선형도의 유일한 불변량 |

### 6.3 해석학적 개념의 GRA bound 조건 분류

| 해석학 개념 | GRA 조건 | 의미 |
|---|---|---|
| 연속성 | modulus 존재 | grade 축적에 유한 bound가 존재 |
| 미분 가능성 | linearity modulus 존재 | grade bound가 **선형** |
| 적분 | bracket 유한 합 | grade의 유한 절단 |
| 완비성 | Cauchy sequence 수렴 | grade의 일관된 극한 |
| 콤팩트성 | cover가 유한 (List) | grade-cut이 이미 구조적으로 유한 |

### 6.4 비가역 화살 (One-Way Arrow)

`cutDouble_no_grade`: 역이분(coarsening)은 ℕ-grade를 가질 수 없다.

GRA 의미: **grade는 축적(+)만 가능하고 감소 불가**.
- 연속체: 정밀도를 올릴 수는 있지만 내릴 수 없다
- P-생성: n = 2a + 3b는 양수만 생성 (0 미포함)
- 물리: 엔트로피 증가의 대수적 그림자

### 6.5 4-Source Modulus 통합

연속(Continuous), Ricci flow, Bracket Cauchy, Zeta의 4가지 modulus가
모두 `IsModulusStructure`로 통합 = 연속체/Ricci/Cauchy/물리 모두가
**같은 GRA 등급 체계의 서로 다른 instantiation**이다.

---

## §7 — 대수적 실현: GRA × Algebra213

### 7.1 GradedRing213

```lean
class GradedRing213 (α : Type) extends Ring213 α where
  grade     : α → Nat
  grade_add : ∀ a b, grade (a + b) ≤ max (grade a) (grade b)
  grade_mul : ∀ a b, grade (a * b) ≤ grade a + grade b
```

- `grade_add`: GRA의 "덧셈 = 등급 보존/상한"
- `grade_mul`: GRA의 "곱셈 = 등급 합산" (cup product 구조)

### 7.2 CD Tower의 GRA Grade 부여

| Algebra213 Layer | GRA Grade | Operad Level |
|---|---|---|
| Int213 (ℤ) | 0 | E₀ (discrete) |
| ZI (ℤ[i]) | 1 | E₁ (loop space) |
| ZOmega (ℤ[ω]) | 1 | E₁ (variant) |
| CDDouble (quaternion-like) | 2 | E₂ (double loop) |
| CDDoubleStar (octonion-like) | 3 | E₃ (triple loop) |

### 7.3 det=1의 삼위일체 (Algebra213)

| 정리 | 대수적 내용 | det=1 의미 |
|---|---|---|
| `normSq_mul` | normSq(uv) = normSq(u)·normSq(v) | norm은 곱에 대해 곱셈적 = 정보 무손실 |
| `ofInt_inj` | embedding이 단사 | scalar 정보가 보존됨 |
| `conj_conj` | involution이 자기역원 | 변환의 가역성 |

이 셋은 모두 "det=1 (정보 보존)"의 서로 다른 대수적 표현이다.

---

## §8 — 차원 증식 프랙탈 (Dimensional Proliferation Fractal)

### 8.1 정의

GRA는 **10 = C(5,3) 방향으로 자기유사**인 차원-추가형 프랙탈이다.

고전 프랙탈이 같은 차원 내에서 축소-반복하는 것과 달리,
GRA 프랙탈은 **매 재귀 단계에서 새로운 직교축을 생성**하면서 자기유사를 만든다.

### 8.2 메커니즘

```
깊이 0:  K_{3,2}^{(c=2)} 하나 — 5 vertices, 12 edges, 3 faces
깊이 1:  C(5,3) = 10개의 이분 분할 → 10개의 독립 GRA 인스턴스
깊이 d:  10^d 방향으로 확장, det=1이 부피 보존
```

### 8.3 det=1의 프랙탈 의미

10방향 확장이 발산하지 않는 이유:
1. P ∈ SL(2,ℤ) → 면적 보존
2. φ² 방향 팽창 ↔ 1/φ² 방향 수축 → 정확히 상쇄
3. "Lens = 10방향 프랙탈에서 하나의 팽창 방향을 고정하는 행위"

### 8.4 범주적 표현

```
GRA_0 = GRA                    (기본 범주)
GRA_1 = GRA^{10}              (10-fold product)
GRA_d = GRA^{10^d}            (d-th iterated product)
Φ : GRA_d → GRA_{d+1}        (volume-preserving functor)
```

---

## §9 — 주기 구조: mod-p와 Adelic 분해

### 9.1 mod-5 주기

P⁵ ≡ −I (mod 5) → P¹⁰ ≡ I (mod 5).

- C(5,3) = 10 (기하학적) = P의 mod-5 주기 (산술적) → **같은 것**
- |SL(2,F₅)| 관련: 120 = 10 × 12 = 이분분할 × edge = 풀 사이클

### 9.2 Adelic GRA

```
GRA_global = ∏'_p GRA_p  (restricted product)
```

- p = 2: NT-축 (fiber parity)
- p = 3: NS-축 (face residue)
- p = 5: d-축 (pentagonal periodicity)
- CRT: (mod 2) × (mod 3) ≅ (mod 6) — gcd=1이 무손실 분해를 강제

---

## §10 — 통합 정리: GRA는 213의 보편 구조이다

### 정리 10.1 (GRA 보편성, 비형식적)

> 213 프레임워크의 모든 수학적 구조는 GRA의 특정 instantiation이다.
> 구체적으로:
>
> (1) **수 체계**: Int213 = Grade-0, Real213 = Grade축, Q213 = Grade-비율,
>     Modulus = Grade-Hom, FSM = Grade-유한, SignedCut = Grade+방향
>
> (2) **해석학**: 연속·미분·적분·완비·콤팩트 = GRA grade의 서로 다른 bound 조건
>
> (3) **대수**: Ring213 hierarchy + CD tower = GRA의 graded algebra 실현
>
> (4) **코호몰로지/Operad/HoTT/그래프**: = GRA의 서로 다른 Reading (R₁~R₄)
>
> (5) **프랙탈 자기유사**: 10방향 증식 = C(5,3) 이분 분할의 재귀적 전개

### 정리 10.2 (Tower Duality)

> GRA Tower(Reading 통합의 상승)와 CD Tower(성질 손실의 하강)는
> 정확한 쌍대(dual)이다. 하나에서 올라간 만큼 다른 하나에서 내려온다.

### 정리 10.3 (=1 삼위일체)

> det(P)=1, gcd(NT,NS)=1, Frobenius=1은 동일한 원리의 세 표현이다:
> - det=1 → 정보 보존 (변환의 가역성)
> - gcd=1 → 보편 생성 (모든 양의 등급 도달)
> - Frobenius=1 → 예외 최소 (도달 불가능 = 출발점뿐)

---

## §11 — 한 문장 요약

> **GRA는 "gcd(2,3)=1인 두 생성자의 가법적 등급 축적"이라는 단일 원리이며,
> 이것이 코호몰로지(cup-grade)·operad(E_n level)·HoTT(truncation)·
> 그래프(walk-length)·해석학(resolution exponent)·대수(CD-grade)·
> 수 체계(Int/Real/Q/Modulus/FSM) 전부에서 동형적으로 나타나는
> 213 프레임워크의 보편 메타 구조이다.**

---

## 관련 파일

### Primary (GRA umbrella)

**Phases 1–6 (universality + translation)**
- `lean/E213/Lib/Math/GRA.lean` — umbrella
- `lean/E213/Lib/Math/GRA/GRAModel.lean` — 7-axiom typeclass + `GRAIso` refl/symm/trans
- `lean/E213/Lib/Math/GRA/Common.lean` — shared PURE Nat helpers (`coprime_2_3`, `reach_23`, `depth_formula`, `ceil3_le_ceil2`)
- `lean/E213/Lib/Math/GRA/NumberTheory.lean` — hub instance on ℕ
- `lean/E213/Lib/Math/GRA/Graph.lean` — R₄ walk-length Reading
- `lean/E213/Lib/Math/GRA/Analysis.lean` — R₅ resolution-exponent Reading
- `lean/E213/Lib/Math/GRA/Cohomology.lean` — R₁ cochain-degree Reading
- `lean/E213/Lib/Math/GRA/HoTT.lean` — R₃ truncation-level Reading
- `lean/E213/Lib/Math/GRA/HigherAlgebra.lean` — R₂ operad-level Reading + universality capstone
- `lean/E213/Lib/Math/GRA/Translation.lean` — master translation + universal depth comparison

**Phases 7–11 (category theory + first enrichment)**
- `lean/E213/Lib/Math/GRA/Category.lean` — 213-native `Cat`-typeclass; `GRACat` (all GRA models); `ReadingCat` (6 closed (2,3)-models); connectedness witness
- `lean/E213/Lib/Math/GRA/Groupoid.lean` — `Groupoid` typeclass on top of `Cat`; every `GRAIso` is invertible; `ConnectedHub` structure; `Reading.hubAtNT` witnesses hub-and-spoke
- `lean/E213/Lib/Math/GRA/Hom.lean` — `GRAHom` (general morphism, not necessarily iso); category laws; forgetful `GRAIso ↪ GRAHom`
- `lean/E213/Lib/Math/GRA/DepthFunctor.lean` — depth as **constant functor** on `ReadingCat`; `Reading_depth_const` proves all 6 Readings agree on `⌈n/3⌉`
- `lean/E213/Lib/Math/GRA/WalkEnrichment.lean` — concrete carrier enrichment for R₄: `EdgeWalk` with bipartite length constraint + `forgetHom : EdgeWalk → Nat` exhibiting the simplified Reading as the image of the enriched one

**Phases 12–15 (full enrichment + naturality + retraction + monoidal)**
- `lean/E213/Lib/Math/GRA/CochainEnrichment.lean` — R₁ enrichment via `Cochain` (cohomological degree)
- `lean/E213/Lib/Math/GRA/HoTTEnrichment.lean` — R₃ enrichment via `Truncation` (homotopy level)
- `lean/E213/Lib/Math/GRA/HigherAlgebraEnrichment.lean` — R₂ enrichment via `Operad` (`E_n` level)
- `lean/E213/Lib/Math/GRA/AnalysisEnrichment.lean` — R₅ enrichment via `Resolution` (analytic exponent)
- `lean/E213/Lib/Math/GRA/Naturality.lean` — translation between enrichments is natural with respect to forgetfuls; `DepthNaturality` capstone bundles depth-preservation for all 5 enrichments
- `lean/E213/Lib/Math/GRA/SectionRetraction.lean` — each forgetful has a section on its valid image (`n = 0 ∨ n ≥ 2`); `WalkRetract` structures the data
- `lean/E213/Lib/Math/GRA/Monoidal.lean` — `product : GRAModel → GRAModel → GRAModel`, the (2, 3)-monoidal product; `trivial23` as unit; `leftUnitHom`/`rightUnitHom` as unit isos

**Phase 16 (Lens bridge — Cat / HoTT as Readings)**
- `lean/E213/Lib/Math/GRA/LensBridge.lean` — `canonicalGradeMap := Raw.fold 2 3 (· + ·)` as the Raw-level (2,3)-arithmetic; all five enrichment grade maps reduce to it; `truncation_operad_grade_agree` proves the HoTT ↔ Higher Algebra Lens-level equation (same Raw-projection, same Lens kernel — they are *one* Reading under different vocabularies)

### Supporting sub-trees (Reading-specific source material)
- `lean/E213/Lib/Math/Analysis/ResolutionShift.lean` — grade-shift formalization (R₅)
- `lean/E213/Lib/Math/Topology/ModulusStructure.lean` — 4-source modulus unification
- `lean/E213/Lib/Math/Real213/Core/ValidCut.lean` — continuum substrate
- `lean/E213/Lib/Math/ParadigmDomainGradedRing.lean` — Ring213 graded hierarchy
- `lean/E213/Lib/Math/CayleyDickson/` — CD Tower (det-loss dual to GRA Tower)
