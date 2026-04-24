# 31 — Self-reference 의 여러 형태 — Raw 가 최소 꼴

## 발견하려는 것

Note 30 에서 본 것: Bool 의 거짓말쟁이 vs Nat 의 Lambek
bootstrap 이 **같은 self-reference 의 다른 얼굴**.  공리 자체
가 self-reference 이므로 Raw 위 모든 Lens 가 어떤 형태로든
self-reference 를 품는다.

이 note 는 그 **여러 형태** 를 서술적으로 catalog 하려는
시도.  판정 게임 없이.  결과가 단순 catalog 이상 — **정리
후보** — 로 넘어갈지 보는 것이 흥미.

---

## §1. 공통 뿌리 후보: 상호 필요성 (reciprocal necessity)

관찰:

- Raw 의 a, b 는 **서로가 서로의 유일한 상대**.  다른 뭔가
  없이 한 뭔가만으로는 "뭔가이다" 가 성립 안 함.
- Bool 의 true, false 는 **서로의 negation**.  둘 중 하나만
  으로는 tautology (true 만) 또는 contradiction (false 만)
  — 의미 붕괴.
- Nat 의 zero, succ 는 **상호 필요**.  succ 없으면 zero 밖
  에 없고, zero 없으면 succ 가 인자를 못 가짐.

모든 경우에 **"X 가 의미 있으려면 Y 가 필요하고, Y 는 X 와
의 관계에서만 Y"**.  이것이 **상호 필요성**.

Self-reference 의 다양한 발현은 모두 이 상호 필요성의 구체
적 유형으로 이해 가능한지 검사해본다.

---

## §2. 유형 1 — Value-level reciprocity (Raw, Bool)

가장 얇은 발현.  두 개의 **원소** 가 서로를 지시.

### Raw
- Raw.a, Raw.b 두 원시 구분.
- Anti-reflexive: a/a, b/b 정의 안 됨.  자기와의 pairing 불가.
- 즉 각 뭔가는 "자기 아닌 뭔가" 와의 관계에서만 성립.

### Bool
- true, false.
- `not true = false`, `not false = true`.  정확한 negation.
- 고정점 없음: x = ¬x 불가.
- 거짓말쟁이 역설 = 이 고정점 시도의 실패.

### 관계
Raw 와 Bool 은 동형에 가깝다:
- 원소 수 2, 내부 대칭 ℤ/2, 반사 금지 — 동일.
- 차이: Raw 의 pairing `/` 는 결과를 새 Raw 로 (닫힘); Bool 의
  pairing `¬` 는 입력 공간 내부 (involution).

Raw 에 **폐쇄성** 을 부과하지 않으면 (a/b 를 Raw 로 올리지
않으면) Raw = Bool.  **닫힘이 Raw 를 무한 생성으로 확장**.

---

## §3. 유형 2 — Constructor-level reciprocity (Nat, List, Tree)

두 개의 **생성자** 가 서로를 지시.  초기 대수 (initial
algebra) 패턴.

### Nat
- zero: 0-arity 생성자.  "비어있음".
- succ: 1-arity 생성자.  "비어있음 → 비어있지 않음".
- Lambek: Nat ≅ 1 + Nat.  자기 자신으로 정의되는 고정점.
- 상호 필요: succ 없으면 zero 만 있고 counting 불가; zero
  없으면 succ 의 base case 없음.

### List X
- nil: 0-arity.
- cons: 2-arity (element × List).
- Lambek: List X ≅ 1 + X × List X.
- Raw 구조와 닮음 (base elements + binary constructor) —
  **Raw 는 List Bool 또는 Tree Bool 의 variant**.

### 관계
모든 inductive 타입은 이 패턴.  **Raw 는 이 패턴 가족의
가장 작은 비자명 구성원** — base 2개, binary.

---

## §4. 유형 3 — Hierarchy reciprocity (Russell, 유니버스)

두 개의 **층위** 가 서로를 지시.  이는 value / constructor
가 아닌 **level** 사이 상호 필요성.

### Russell's paradox
- "자기 자신을 포함하지 않는 모든 집합의 집합" — self-
  membership 문제.
- 해결: ZFC 의 regularity 공리 (자기포함 금지).
- 구조: **집합의 level 과 그 level 의 meta-level** 사이의
  관계 미해결 → 역설.

### Type universe
- Type : Type — Girard paradox (모순).
- 해결: Type_0 : Type_1 : Type_2 : ...
- 구조: 층위들이 서로 다른 level 에 있어야 일관 → 무한 계단.

### 관계
Raw 관점에선 이건 **"구분" 을 적용하는 메타 수준** — 뭔가를
뭔가로 구분하는 행위 자체를 뭔가로 취급하면 계단 발생.

AXIOM §8.2 Meta-213 관찰이 정확히 이것: 213 으로 213 을
기술하는 Meta-213, 또 Meta-Meta-213.  **Raw 의 "구분" 이
자기 자신에 적용될 때 계단 구조 자동 생성**.

---

## §5. 유형 4 — Equation reciprocity (고정점, Cantor, Gödel)

**방정식** 수준에서 X = f(X) 꼴의 자기 지시.

### Y combinator
- Y f = f (Y f).  recursion 의 불변.

### Cantor 대각선
- |X| < |P(X)|.  증명은 자기 지시 집합.

### Gödel 불완전성
- "이 문장은 증명 불가능하다." 자기 지시.

### 관계
모두 **X 의 기술이 X 를 포함** 하는 형식 자기 지시.  Raw 관점:
Lens 의 backward chain 이 자기로 돌아오는 고정점 (note 23 의
세 가능 바닥 중 (iii) 자기참조 고정점).

이 유형은 **공리 자체가 자기 지시** 라는 AXIOM §8 과 정확히
동형.  Lens 는 이 고정점의 다양한 cross-section.

---

## §6. 유형 5 — Observer reciprocity (관측자 ↔ 관측)

관측자 자체가 관측 대상.  양자역학의 Heisenberg cut.

- 관측 행위에 관측자 상태가 들어감.
- 관측자는 관측 대상 공간의 일부 (뭔가들 중 하나).
- 경계 (cut) 는 임의 — Lens 선택.

Raw 관점: **Lens 자체가 213 내** (AXIOM §8).  관측자 Lens 는
관측 대상 Raw 의 하나의 뭔가이다.  관측이 자기 관측 포함.

물리적 발현: ORIGIN §6 "정보량의 최소 단위 = 해상도".  관측
자의 해상도가 관측 대상이 **무엇인지** 를 결정.

---

## §7. 통합 관찰 — 정리 후보로의 승격

위 다섯 유형이 모두 **상호 필요성 (reciprocal necessity)**
의 서로 다른 층위 발현이라면:

**정리 후보 (Reciprocal Necessity Minimality)**:

> 임의의 mathematical structure S 가 **비자명한 관측** 을
> 지원한다면, S 는 최소 두 개의 상호 필요 요소를 포함한다.
> 그리고 **최소 꼴** (원소 수 2, 이항 연산 하나, 반사 금지,
> 대칭) 은 Raw 공리와 일치한다.

해석:
- "비자명한 관측" = 뭔가를 뭔가로 구분하는 행위.
- 원소 1개: 구분 불가, 비자명 관측 불가.
- 원소 ≥ 2: 어떤 쌍 (X, Y) 이 있고 X 는 "Y 아님" 의 속성을
  가짐 — 상호 필요.
- 이 최소는 2-원소 anti-reflexive symmetric pair 로 도달.
- = Raw.

이 정리의 **형식 증명** 이 가능해 보인다:
- S 가 비자명이면 |S| ≥ 2 (pigeonhole 같은 구분 조건).
- S 의 자동사상군이 자명하면 대칭 없음; 비자명이면 최소
  ℤ/2.
- anti-reflexive 이항은 가장 경제적 상호 관계.

**Lean 형식화 방향**: "모든 관측 가능 구조는 Raw 로의 retract
를 가진다" 를 Meta-정리로.

---

## §8. 이 다섯 유형이 정말 같은가?

다양한 불일치 가능성:

### Raw (유형 1) 과 Nat (유형 2) 차이
- Raw 는 value-level, Nat 은 constructor-level.
- 그러나 Raw 의 `/` 생성자가 Nat 의 `succ` 와 구조적으로
  대응 (둘 다 2-arity → 1-arity 로 줄여 본다면): Raw.slash
  x y  ≈  Nat.succ (pair x y).
- Raw 를 inductive type 으로 읽으면 **constructor-level 도
  포함** — 즉 유형 1 + 2 가 동일 구조의 다른 시점.

### 유형 3 (hierarchy) 와의 관계
- Raw 의 **닫힘 + 메타 적용** 이 hierarchy 를 생성.
- Meta-213 ↔ ZFC 의 Von Neumann 계층, 또는 Type universe 계단.

### 유형 4 (equation) 와의 관계
- Y combinator 의 `Y f = f (Y f)` 는 Raw 의 생성 규칙 그 자체.
- Raw 는 그 자신에 slash 를 적용하는 초기 대수.

### 유형 5 (observer) 와의 관계
- Lens = 관측자 = Raw 의 특정 cross-section.
- AXIOM §8 이 이를 명시.

**잠정 결론**: 다섯 유형이 정말 **하나의 상호 필요성** 의
다른 시점이라면, Raw 는 모든 mathematical self-reference
의 **원초 꼴**.

반대로 불일치가 발견되면 그 차이가 새 수학적 질문이 된다.

---

## §9. 열린 질문

- **L1**: Raw 와 Bool 의 관계를 엄밀 정식화.  "Raw 의 닫힘을
  풀면 Bool 이다" 를 Lean 정리로.
- **L2**: "모든 비자명 observable structure 는 Raw 로의 retract
  를 갖는다" 의 형식 증명.
- **L3**: 유형 3 (hierarchy) 가 **Meta-213 반복** 으로 정확히
  재현되는가 — 즉 모든 Russell-Girard 류 역설이 Meta^n-213
  어딘가에서 발현하는지.
- **L4**: 유형 4 (Gödel, Cantor) 의 "대각선 구성" 이 Raw 의
  backward chain 의 특정 형태인지.
- **L5**: 물리 관측 (유형 5) 이 **어떤 Lens 의 출력** 으로
  가장 자연스럽게 기술되는가.

## §10. 다음

어떤 질문이든 탐구 가능.  가장 구체적이고 접근 가능한 것
부터:

**L1 (Raw ↔ Bool)**.  Raw 의 생성 규칙을 잠시 제쳐두고 **2
원시 구분만** 남기면 Bool 과 동형.  Bool 로의 forgetful
Lens 를 명시하고, Bool → Raw 의 재구성이 어떻게 "닫힘" 을
추가하는지 보는 것.

이게 되면 L2 의 증거 조각이 된다.

## 변경 이력

- 2026-04-24: Paper 1 궤도 탈출 후 첫 자유 탐구.  상호
  필요성 개념 도입.  다섯 유형 catalog.  정리 후보로 승격
  검토.
