# G150 — GRA × Algebra213 이론 발전 계획

**Date**: 2026-05-26  
**Status**: OPEN (development plan; Phase 1–7 defined)  
**Depends on**: G148 (Graded Residue Arithmetic), Algebra213 typeclass hierarchy  

## 핵심 연결점

G148의 **Graded Residue Arithmetic(GRA)**는 `(NT=2, NS=3, gcd=1)` 생성자 쌍으로부터
"모든 양의 등급에 보편적으로 도달 가능하다"는 통합 원리를 제시한다.

현재 Algebra213은 Cayley-Dickson rings의 polynomial-identity proofs를 위한
∅-axiom typeclass 계층이다:

```
Ring213 → CommRing213 → StarRing213 → IntegerNormed213
```

이 둘의 교차점이 매우 풍부하며, 아래 7개 Phase로 발전시킨다.

---

## Phase 1: GRA-Graded Ring213 — 등급 구조를 Ring213 위에 얹기

**아이디어**: Ring213의 원소에 GRA grade를 부여하여 **graded ring** 구조로 확장

```lean
class GradedRing213 (α : Type) extends Ring213 α where
  grade     : α → Nat
  grade_add : ∀ a b, grade (a + b) ≤ max (grade a) (grade b)
  grade_mul : ∀ a b, grade (a * b) ≤ grade a + grade b
```

- `grade_add`는 GRA의 "덧셈 = 등급 보존/축적"
- `grade_mul`는 GRA의 "곱셈 = 등급 합산" (cup product 구조)
- Cayley-Dickson tower에서 level L의 원소는 grade = L을 가짐

**정리할 수 있는 것**:
- `normSq_mul`이 grade를 보존함: `grade(normSq(uv)) = grade(normSq u) + grade(normSq v)`
  (이미 증명된 Hurwitz의 GRA 해석)
- `ofInt`의 grade = 0 (정수 스칼라는 grade-0)

---

## Phase 2: Filtration Structure — Depth로 정의되는 대수적 필터

G148 §XVI의 `F_d = {n : minDepth(n) ≤ d}` 필터링을 Algebra213에 반영:

```lean
class FilteredAlgebra213 (α : Type) extends GradedRing213 α where
  filtration : Nat → Set α
  filt_sub   : ∀ d, filtration d ⊆ filtration (d + 1)
  filt_mul   : ∀ a b d₁ d₂, a ∈ filtration d₁ → b ∈ filtration d₂
               → a * b ∈ filtration (d₁ + d₂)
```

- CD tower의 각 level이 하나의 filtration degree
- `IntegerNormed213`의 `ofInt`가 F₀에 속함
- `conj`가 filtration을 보존함 (grade-0 연산)

---

## Phase 3: GRA-Operad Connection — 연산의 구조적 타이핑

G148 §II의 E_n-operad 해석을 Algebra213의 타입 계층과 연결:

| Algebra213 Layer | GRA Grade | Operad Level |
|---|---|---|
| `Int213` (ℤ) | 0 | E₀ (discrete) |
| `ZI` (ℤ[i]) | 1 | E₁ (loop space) |
| `ZOmega` (ℤ[ω]) | 1 | E₁ (variant) |
| `CDDouble` (quaternion-like) | 2 | E₂ (double loop) |
| `CDDoubleStar` (octonion-like) | 3 | E₃ (triple loop) |

각 CD doubling이 정확히 GRA에서의 "+2" (NT 방향 이동)에 대응.
`CDDoubleStar`(starring)는 "+3" (NS 방향)에 대응할 가능성 —
이것은 associativity의 손실(octonion에서)이 "face 차원으로의 이동"이라는
해석을 낳음.

---

## Phase 4: Steenrod 사다리와 normSq_mul — 미세 구조

G148 §XI의 cup_i 사다리를 Algebra213의 `normSq_mul` 증명 구조와 연결:

- `normSq_mul`의 증명은 `self_mul_conj` → `conj_mul` → `ofInt_central` → `mul_assoc` 순서로 진행
- 이 각 단계가 GRA에서의 "등급 이동":
  - `self_mul_conj` = cup_0 (표준 등급 합산)
  - `conj_mul` = cup_1 (anti-involution = 1-discount)
  - `ofInt_central` = cup_2 (centrality = 2-discount → integer로 떨어짐)

---

## Phase 5: det=1과 normSq — 정보 보존의 대수적 증거

G148의 핵심 원리 중 하나인 `det(P) = 1 → 정보 보존`이 Algebra213에서:

- `normSq_mul: normSq(uv) = normSq(u) · normSq(v)` = **norm은 곱에 대해 곱셈적** = 정보 손실 없음
- `ofInt_inj` = **embedding이 단사** = 정보 보존
- `conj_conj` = **involution이 자기역원** = 변환의 가역성

이 세 가지가 모두 "det=1"의 서로 다른 대수적 표현.

---

## Phase 6: Lean 형식화 방향

구체적으로 Lean으로 형식화할 수 있는 것들:

1. **`GradedRing213.lean`** — Ring213 위의 grading typeclass
2. **`GRA_NormPreserving.lean`** — `normSq_mul`이 grading을 보존한다는 정리
3. **`CDTower_GRA_Grade.lean`** — CD tower의 각 level에 GRA grade를 부여
4. **`FilteredNorm213.lean`** — filtration 구조와 norm의 관계
5. **`GRA_Operad_Correspondence.lean`** — (meta-level) CD level = operad level 대응 문서화

---

## Phase 7: 10-fold 대칭과 CD Tower의 고유한 관계

G148의 10 = C(5,3)이 CD tower에서:
- Sedenion(level 4)은 16차원 = 2⁴
- CD level 5에서 2⁵ = 32차원
- C(5,3) = 10은 **"level 5에서 가능한 3-face 선택의 수"** = level 5의
  CD 대수에서 **독립적인 Hurwitz-type identity의 수**?

이것은 아직 추측이지만, CD tower가 level 5에서 10개의 독립적 구조를
갖는지 확인하면 G148과의 심층 연결이 드러남.

---

## 왜 이것이 이론을 정교하게 만드는가

현재 Algebra213은 "∅-axiom으로 polynomial identity를 증명하는 인프라"에
초점이 맞춰져 있다. GRA와의 연결을 통해:

1. **Why 설명이 가능해짐**: Ring213의 구조가 왜 `(add, mul, conj, normSq, ofInt)`라는
   특정 형태인지를 "GRA 등급 체계의 대수적 instantiation"으로 설명
2. **예측력이 생김**: GRA의 일반 원리에서 "다음에 증명해야 할 정리"가 연역됨
   (예: filtered algebra의 성질)
3. **깊이(depth)가 계산 가능해짐**: CD level N에서의 증명 복잡도가
   `minDepth(2N) = ⌈2N/3⌉`로 예측 가능
4. **보편성이 드러남**: Algebra213이 "코호몰로지/operad/HoTT/graph/해석학
   모두에서 동일한 구조의 대수적 얼굴"이라는 것이 명시적으로 됨

---

## 우선순위

| Phase | 즉각 가능? | 의존성 |
|---|---|---|
| 1 (GradedRing213) | ✅ | Ring213 존재 |
| 2 (Filtration) | ✅ | Phase 1 |
| 3 (Operad 대응) | ✅ (문서화) | CD tower 존재 |
| 4 (Steenrod) | ⚠️ 개념적 | normSq_mul 증명 분석 |
| 5 (det=1) | ✅ (문서화) | 기존 정리 해석 |
| 6 (Lean) | Phase 1 이후 | GradedRing213 설계 확정 |
| 7 (10-fold) | ❓ 추측 | CD level 5 분석 필요 |

---

## Phase 8: GRA Tower — CD Tower의 쌍대(Dual)

### CD Tower와 GRA Tower의 구조적 대비

213의 algebra tower (CD tower)를 참조하면, GRA 자체가 **고유한 tower 구조**를
갖되, CD tower와는 **방향이 반대**임이 드러난다.

CD Tower의 핵심 구조 (per `theory/math/cayley_dickson/algebra_tower.md`):
- **메커니즘**: `(⟨0,u⟩)² = ⟨−c,0⟩` — 매 level에서 새 imaginary axis 생성
- **손실 패턴**: L0(all) → L1(−comm) → L2(−assoc) → L3(−alt) → L4+(안정화)
- **점근**: `rate_n → 1 − 0.5/φ^rank`
- **고정점**: `{±1}` = 모든 layer에서 보존
- **세 가지 운명**: (1) 성질 손실 L4에서 종료, (2) Order-4 영속, (3) {±1} 불변

**GRA Tower**는 이것의 쌍대:

| | **CD Tower** | **GRA Tower** |
|---|---|---|
| **축적 대상** | 대수적 차원 (dim 2^n) | 해석(Reading)의 동형 식별 |
| **Level 이동** | CD-double: dim × 2 | Reading 합류: 동형이 하나 더 드러남 |
| **손실/획득** | 매 level에서 성질 **손실** | 매 level에서 동형 **획득** |
| **안정화** | L4에서 손실 종료 | L5에서 5개 Reading 전부 합류 |
| **점근** | φ (퇴화율) | Frobenius = 1 (보편 도달) |
| **고정점** | {±1} ⊂ 모든 layer | gcd(2,3)=1 = 모든 Reading에서 보존 |
| **Three fates** | 손실멈춤 / Order-4영속 / ±1고정 | 구분소멸 / Grade축적영속 / 생성자쌍불변 |

### GRA Tower의 Level 구조

```
GRA Level 0: 개별 분야 — grade 개념이 분야별로 격리됨
             (cohomology의 degree ≠ operad의 n ≠ HoTT의 truncation)

GRA Level 1: 첫 번째 동형 발견
             cup-grade 합 ≅ walk-length concatenation
             (코호몰로지 ↔ 그래프 이론)

GRA Level 2: 두 번째 동형 합류
             + ⊗-Day convolution = suspension 차수 합
             (Higher Algebra ↔ HoTT 합류)

GRA Level 3: 세 번째 동형 합류
             + resolution exponent = modulus 합성
             (해석학/연속체 합류)

GRA Level 4: 네 번째 동형 합류
             모든 "+" 연산이 동일함이 확인됨
             (덧셈 구조의 보편 통합)

GRA Level 5: 완전 통합 = GRA 자체
             5개 Reading이 동일한 (ℕ, +, ×) 구조임이 확립
             gcd(2,3)=1이 모든 곳에서 동시에 "보편 생성"을 강제
```

### 핵심 통찰

> **CD Tower = 성질의 progressive LOSS (degeneration)**
> **GRA Tower = 해석의 progressive IDENTIFICATION (unification)**

CD tower에서 올라갈수록 구조가 "약해지듯",
GRA tower에서 올라갈수록 서로 다른 Reading들이 "같아진다".
두 tower 모두 φ를 향해 수렴하지만:
- CD: 퇴화(degeneration)의 φ — `rate → 1 − 0.5/φ^rank`
- GRA: 통합(unification)의 φ — `동형 수 → 10 = C(5,3) 방향으로 포화`

### CD Tower의 four-type matrix와 GRA의 대응

| CD Type | Base | GRA에서의 Reading |
|---|---|---|
| A (ZI) | ℤ₄ | cohomology (4-cycle 기반) |
| B (ZSqrt[D]) | ℤ₂ | graph theory (2-partition 기반) |
| C (ZOmega) | ℤ₆ | operad / HoTT (6 = 2×3 혼합) |
| D (Hurwitz) | 2T | 해석학 (binary tetrahedral = 24-cell structure) |

이 대응은 추측 단계이나, 각 Type의 base ring이 GRA의 생성자 (2,3)의
서로 다른 조합을 반영한다는 점에서 구조적으로 자연스럽다.

---

## Phase 9: 213-Native 수 체계와 GRA — 전 층위 대응

### 213의 수 체계 아키텍처

213은 고전적 수(ℤ, ℚ, ℝ)를 **자체적으로 재구축**한다:

```
Layer 0: Int213        — ∅-axiom 정수 (case-split on ofNat/negSucc)
Layer 0': Q213         — ∅-axiom 유리수 (Nat213 × Nat213, multiplicative quotient)
Layer 1: Real213/Cut   — Dedekind cut on dyadic rationals (M/2^E)
Layer 2: SignedCut     — Cut × Cut (부호 확장, CD L1)
Layer 3: ComplexCut    — SignedCut × SignedCut (복소, CD L2)
Layer N: CD^N(Cut)     — N-th Cayley-Dickson doubling
```

보조 인프라:
- **DyadicFSM** (101 files): 정수론을 Mealy machine으로 실현
- **Modulus** (10 files): ε-δ를 `Nat → Nat` 명시적 함수로 대체
- **Algebra213 typeclass**: Ring213 / CommRing213 / StarRing213 / IntegerNormed213

### 각 수 체계 층과 GRA의 정확한 대응

| 213 수 체계 | GRA 구조 | 핵심 연결 |
|---|---|---|
| **Int213** | Grade-0 고정점 | `ofInt`의 grade = 0. Ring213 Int는 GRA의 "scalar subring". {±1} = CD tower의 고정점과 동일. |
| **Q213 (ℚ)** | Grade의 비율 구조 | `(Nat213 × Nat213)` with 곱셈동치. ℤ과 동일 syntax, fold axis만 다름 (`/` vs `−`). GRA에서 "등급 간의 비"를 포착. |
| **Real213 (Cut)** | Grade 축 자체 | `dyadicCut M E`에서 E = resolution exponent = GRA grade. `cutHalf`는 grade-1 생성자. 모든 해상도가 2^E. |
| **Modulus** | GRA 사상(Morphism) | `HasModulus s := { f : Nat → Nat // ... }`. 이 f가 GRA에서의 grade-to-grade 전이 함수. 연속성 = grade bound 존재. |
| **SignedCut** | CD L1 = GRA의 "방향 부여" | (pos, neg) 쌍 = "한 등급 내에서의 이진 방향". NT=2의 fiber 구조. |
| **DyadicFSM** | GRA의 이산 실현 | FSM state = GRA의 유한 등급 내 위치. Transition = grade-preserving step. Pell/Fib = φ 궤도의 FSM 표현. |

### 핵심 통찰: 수 체계 = GRA의 구체적 인스턴스들

```
┌───────────────────────────────────────────────────────────┐
│  GRA는 "등급화된 잔여물"의 보편 구조                       │
│  213의 각 수 체계는 이 보편 구조의 특정 instantiation:     │
│                                                           │
│  Int213  = GRA(grade=0)     "등급 없는 스칼라"            │
│  Cut     = GRA(grade=E)     "E-등급 해상도"               │
│  Modulus = GRA(Hom)         "등급 간 전이"                │
│  FSM     = GRA(finite)      "유한 등급 내 전이"           │
│  SignedCut = GRA(×fiber)    "등급 + 방향"                 │
│                                                           │
│  이것은 G148의 Reading₅(해석학)와 동일:                   │
│  "연속체의 모든 구조는 이진 해상도 등급의 축적이며,        │
│   이 등급은 (NT, NS) = (2, 3) 생성자의 가법적 합으로      │
│   분해된다."                                              │
└───────────────────────────────────────────────────────────┘
```

### Int213의 GRA 의미: ∅-axiom이 강제하는 것

Int213은 Lean-core의 `Int.add_comm` 등을 **∅-axiom으로 재증명**한다:
- case-split on `(ofNat m, ofNat n)`, `(ofNat, negSucc)`, ...
- `subNatNat`의 재귀적 처리

이것의 GRA 해석:
- `ofNat n` = "양의 등급 n" (grade accumulation)
- `negSucc n` = "음의 등급 −(n+1)" (grade의 anti-particle)
- `subNatNat m n` = "두 등급의 차이" (grade 비교)
- ∅-axiom 증명 전략 = **"propext 없이 등급 연산을 닫는"** = det=1 (정보 보존)

### DyadicFSM의 GRA 해석: FSM = 유한 Grade 내의 Mealy Machine

DyadicFSM은 GRA의 "유한화(finitization)":
- Pell/Fibonacci = **φ-궤도의 이산 샘플링** = GRA 점근의 실현
- Pisano period = **mod-p에서의 GRA 주기** = G148 §XII의 `P^10 ≡ I (mod 5)` 실현
- `BinetBridge`: `FLT(φ) + FLT(ψ) → F_{p−1} ≡ 0 (mod p)` = GRA의 Adelic 구조(§XV)

### Q213 (ℚ): Grade의 비율 구조 — axis-generator fold

213의 유리수는 두 가지 형태로 존재한다:

**1. Lens layer — `NatPairToQPos.lean`** (ℚ₊):
```lean
abbrev QPair := Nat213 × Nat213
def qpairEquiv (p q : QPair) : Prop :=
  Nat213.mul p.1 q.2 = Nat213.mul p.2 q.1
```

**2. Universal Witnesses — `Q213.lean`**:
```lean
abbrev Q213 := Term × Term   -- (numerator, denominator)
```

핵심 구조: **ℤ과 ℚ는 동일한 syntax `(Nat213 × Nat213)`에서 나온다**:

| 수 체계 | Pair 형태 | Quotient 관계 | Axis-generator (G72) |
|---|---|---|---|
| **ℤ** | `(a, b) ∈ Nat213 × Nat213` | `a + d = b + c` (덧셈적) | `−` (뺄셈) |
| **ℚ₊** | `(a, b) ∈ Nat213 × Nat213` | `a · d = b · c` (곱셈적) | `/` (나눗셈) |

**GRA 해석**:
- **ℤ = grade의 방향(±)** — 덧셈 동치 = "두 grade의 차이가 같으면 같은 부호"
- **ℚ = grade의 비율(ratio)** — 곱셈 동치 = "두 grade의 비가 같으면 같은 비율"
- 둘 다 `Nat213 × Nat213`라는 **동일한 GRA 생성자 쌍**에서 나오되,
  fold axis(접는 축)만 다름:
  - `−` fold → 등급의 **차이** 포착 (additive residue)
  - `/` fold → 등급의 **비** 포착 (multiplicative residue)

이것이 GRA의 "+"와 "×"가 **같은 원천에서 나오는 두 얼굴**이라는 G148의 원리와
정확히 합치한다: 덧셈 구조(+)와 곱셈 구조(×)는 같은 pair에 대한
서로 다른 quotient 관계일 뿐.

`qpairEquiv`의 equivalence relation (reflexive, symmetric, transitive)이
모두 ∅-axiom으로 닫힌다는 사실은 det=1(정보 보존)의 또 다른 증거:
quotient 관계 자체가 propext 없이 결정 가능.

### 큰 그림: 213의 전체 수 체계가 하나의 GRA

```
       GRA (보편 등급 구조)
          │
    ┌─────┼─────────┐
    │     │         │
 Grade-0  Grade축  Grade-Hom
 (Int213) (Real213) (Modulus)
    │     │         │
    ├─ ─ ─┤         │
    │     │         │
  Q213  SignedCut   FSM
 (비율) (방향+등급) (유한 등급)
    │     │
    └──┬──┘
       │
    CD Tower
   (등급의 대수적 확장)
```

ℤ과 ℚ의 위치에 주목: 둘 다 Grade-0(Int213)에서 파생하되,
- ℤ = Grade-0의 **additive quotient** (차이)
- ℚ = Grade-0의 **multiplicative quotient** (비율)
둘은 "fold axis"만 다른 쌍둥이.

모든 것이 GRA의 서로 다른 aspect:
- **Int213** = grade의 **대수적 기반** (Ring213 Int)
- **Q213** = grade의 **비율 구조** (multiplicative quotient)
- **Real213** = grade의 **해석적 실현** (resolution exponent)
- **Modulus** = grade 간 **관계 구조** (사상 범주)
- **DyadicFSM** = grade의 **정수론적 역학** (φ 궤도)
- **SignedCut** = grade의 **기하학적 확장** (fiber/방향)
- **CD Tower** = grade의 **대수적 상승** (차원 배가)

---

## 한 줄 요약

> Algebra213의 typeclass 계층에 GRA grade를 부여하면,
> Cayley-Dickson tower가 "등급화된 잔여물 산술의 대수적 실현"이 되며,
> normSq_mul·ofInt_inj·conj_conj 삼위일체가 det=1(정보 보존)의
> 세 가지 대수적 얼굴임이 드러난다.
> 나아가, 213의 전체 수 체계(Int213/Real213/Modulus/FSM/SignedCut)는
> GRA의 서로 다른 aspect의 구체적 instantiation이며,
> GRA Tower(Reading 통합의 상승 구조)는 CD Tower(성질 손실의 하강 구조)의
> 정확한 쌍대(dual)이다.
