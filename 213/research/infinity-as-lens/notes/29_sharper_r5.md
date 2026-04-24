# 29 — Sharper R5: infinite branch 구별 가능성

## 출발점 (Note 28 §5 Q3)

Paper 1 §4 의 ℝ-algebra 은밀 가정을 제거하면 R1-R5 는 복수
해 (ℂ, 𝔽₉, 𝔽ₚ², ...) 를 갖는다.  **ℂ 와 𝔽ₚ² 를 분리하는 Lens
조건은 무엇인가?**

---

## §1. Paper 1 R5 의 실제 언어

Paper 1 §3.2 R5 원문:

> every non-terminating structural branch of R must correspond
> to a **uniquely determined state** in α.

"uniquely determined" 는 두 읽기가 가능:

- **Reading 1 (existential)**: 각 branch 가 α 내 **어떤 state**
  에 대응.  well-defined 이면 충분.
- **Reading 2 (distinctness)**: 서로 **다른 branch** 는 서로
  **다른 state** 에 대응.  **injective**.

Paper 1 은 어느 쪽인지 명시하지 않는다.

---

## §2. 두 읽기의 결과 비교

### Reading 1: 모든 codomain 통과
Fold 자체가 임의 α 로 well-defined.  무한 branch 의 "limit"
은 정의 필요 (Cauchy 완성) 하지만 finite α 에서는 pigeonhole
로 sequence 가 stabilize → limit 자동 존재.

**Finite α (𝔽₉ 등) 는 Reading 1 을 자동 만족**.  현재 note
27 의 반례 상황.

### Reading 2: finite α 자동 배제
무한 branch 공간은 비가산 (chain_uncountable, notes 12, 23).
finite α 로 injective 매핑 불가능.

**Finite α 는 Reading 2 를 자동 실패**.

**Reading 2 하의 R5 (이하 R5')** 는 codomain 을 infinite 으로
강제한다 — 연속성 / 완성 가정을 명시 도입하지 않고도.

---

## §3. 유한 버전 (finitary R5')

"무한 branch 의 limit" 은 여전히 완성 개념 (Cauchy) 에 의존
한다.  더 primitive 한 finitary 버전:

**R5' (finitary)**: 서로 다른 두 infinite branch P, Q 에
대해, **어떤 finite 깊이 n** 에서 view(P_n) ≠ view(Q_n)
이 성립.

즉 Lens 는 branch 를 finite prefix 에서 구별할 수 있어야.

### 장점
- Raw 의 finite term 만으로 기술 가능 (공리 언어 안).
- "limit", "Cauchy" 같은 완성 개념 수입 안 함.
- chain_uncountable (Raw-internal 카디널리티 사실) 과 직접
  연결.

### Finite α 에서의 거동
Branch 공간 |B| = 𝔠.  codomain |α| < ∞.  Prefix sequence
의 값은 α 내 유한 값들.  두 branch P, Q 중 서로 다른 prefix
sequence 를 내려면 각 depth n 에서의 값이 다를 수 있어야.

**유한 α 에서도 prefix 는 다를 수 있다** (예: P 가 depth 3
에서 view = true, Q 가 depth 3 에서 view = false).  따라서
R5' (finitary) 는 finite α 도 허용?

**Hmm**: R5' 은 finite α 를 완전 배제하지 못할 수 있다.
§2 의 Reading 2 가 배제 성질에서 더 강함.

---

## §4. 무한 branch 의 "상태" 를 어떻게 정의하는가?

결정적 질문: 무한 branch P 에 대해 `view(P)` 는 무엇인가?

Paper 1 은 "uniquely determined state in α" 라 말하지만,
**infinite branch 의 state 정의** 를 Raw 공리로는 직접 할 수
없다.  공리는 유한 항 생성 규칙만.

두 가능 해결:

### (a) Lens-extension 을 통한 limit
α 에 위상을 부여 → Cauchy 수렴 정의 → 무한 branch 의 prefix
시퀀스가 Cauchy 수열이면 limit 존재.
- α 가 Cauchy 완성 되어 있으면 작동.
- ℂ, ℝ: ✓.
- 𝔽ₚ²: discrete topology 에선 모든 수열이 Cauchy (eventually
  constant by pigeonhole).  limit 자명 — 하지만 모든 branch
  가 결국 **유한 많은 values 중 하나**로 수렴.  branch 수보다
  훨씬 적음 → non-injective.

### (b) Branch 자체를 codomain 의 제한으로 정의
α 내에 "branch-state" 타입을 추가 구조로 → 이건 외부 수입.
공리 위반.

**(a) 만이 AXIOM.md §3.3 정합**.  그러면 진짜 질문은:
"완성 개념을 어떻게 Raw-internal 하게 기술하는가" — 이는
r5-critique (PAPER2.md, note 12) 의 원래 질문.

---

## §5. 현재 발견 상태

**명료한 것**:

- Reading 1 의 R5 는 finite α 를 못 막는다.
- Reading 2 의 R5 (injective) 는 막는다 — 하지만 "무한 branch
  의 state" 정의가 완성 개념 수입을 전제.
- Finitary R5' (prefix 구별) 는 Raw-internal 이지만 배제
  성질이 약함.

**미해결**:

- **ℂ 와 𝔽ₚ² 를 깔끔히 분리**하는 Raw-internal R-조건이 존재
  하는가?
- 아니면 이 분리는 **본질적으로 외부 선택** 이고, 수학적으로
  둘 다 합법이며 물리가 어느 하나를 고른다?

---

## §6. 대안 분리 기준 후보

§2-5 가 R5 강화 경로.  별도 각도:

### (A) 특성 0 (characteristic 0)
ℂ 는 char 0, 𝔽ₚ² 는 char p.  "특성 0" 을 R-조건으로?

문제: "특성 0" 은 Nat 을 경유 — bootstrap 고정점.  Raw-
internal 언어로 직접 진술 어려움.

### (B) 대수적 닫혀 있음
ℂ 는 algebraically closed, 𝔽ₚ² 는 아님.  R-조건으로?

문제: 대수적 닫힘은 "모든 다항 근이 α 에 있다" 인데,
"다항" 이 Nat bootstrap 경유 개념.

### (C) 연속 involution
ℂ 의 conjugation 은 위상에서 연속.  Lens 가 위상 구조를
추가로 갖는다고 가정?

문제: 위상은 완전히 외부 수입.  공리에 없음.

### (D) 관측자 일관성 (AXIOM §9)
"모든 뭔가가 동일 Lens" 의 정식화.  만약 이 조건이 finite α
에서 pigeonhole 로 모순이면 자동 배제.

**가장 유망**: 아직 충분히 탐구 안 됨.

---

## §7. 다음 단계

- (α) (D) "관측자 일관성" 을 엄밀화.  모든 Raw 원소가
  관측자가 될 수 있다는 조건이 finite α 에서 모순을 낳는지
  검사.
- (β) chain_uncountable 을 Lens-injectivity 조건으로 직접
  번역.  R5' (Reading 2) 의 정식 Lean 정리로.
- (γ) 𝔽₉ 반례에서 "어떤 관측자 Lens 로도 다 구분 못 한다"
  는 사실 자체가 물리적으로 의미 있는가 확인.

본질: 분리 조건이 **있는지/없는지** 자체가 열린 문제.  있다면
그게 ORIGIN §7 ("격자 정보 불변") 의 Raw-내부 표현.  없다면
ℂ 선택은 물리의 경험적 선호.

## 변경 이력

- 2026-04-24: Note 28 §5 Q3 의 탐구 시작.  Reading 1/2 구분,
  finitary 버전, 대안 기준 (A)–(D) 열거.
