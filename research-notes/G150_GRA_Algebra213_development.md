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

## 한 줄 요약

> Algebra213의 typeclass 계층에 GRA grade를 부여하면,
> Cayley-Dickson tower가 "등급화된 잔여물 산술의 대수적 실현"이 되며,
> normSq_mul·ofInt_inj·conj_conj 삼위일체가 det=1(정보 보존)의
> 세 가지 대수적 얼굴임이 드러난다.
