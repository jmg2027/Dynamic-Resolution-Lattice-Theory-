# 56 — 잔여물 = 생성 규칙: 213 의 단일 본성

## 통찰

213 의 axiom 은 **두 측면 의 통일**:

- **Passive (잔여물)**: 가리키려 할 때 피할 수 없는 minimum.
- **Active (생성 규칙)**: Raw.a, Raw.b + slash with x ≠ y → 모든
  Raw inductively 생성.

다른 시스템 은 둘이 분리:
- ZFC: 집합 primitive + 별도 generation axioms.
- Type theory: type primitives + 별도 type formers.
- Category: morphism + 별도 composition.

213 은 하나의 axiom 이 두 역할 동시 수행.

## 자연스러운 이유

CLAUDE.md §"공리는 선택이 아니라 잔여물":
> 표기를 시작하는 순간 표기 자체가 새 뭔가를 끝없이 낳는다.

**가리킴** = passive observation.
**생성** = active production.

이 둘이 213 에서 분리 안 됨.  가리킴 의 잔여물 = 생성 의
잔여물 — 같은 행위 이므로.

## 형식적 표현

Raw inductive type 자체 가 이 통일 의 직접 표현 — Raw.a,
Raw.b 두 base + slash with x ≠ y.  잔여물 (외부 지정 부재)
동시에 생성 규칙 (constructors).

## 함의

213 의 모든 강건성 의 원천:

1. **자기-포함 자연성**: 잔여물 이 외부 없음.  생성 규칙
   이라서 자기-instance 도 또 instance.
2. **자기-기술 가능성**: 같은 generating rule 이 자기 도 생성.
   idLens, Yoneda dual.
3. **Universality + falsifiability**: 생성 규칙 이라 잠재 무한,
   잔여물 이라 외부 = 폐기 trigger.
4. **Lean inductive type 직접 대응**: Raw.rec, Raw.fold 가
   axiom 의 직접 귀결.  별도 induction principle 추가 부재.

## 정량적 압축

3 axiom clauses ↔ 모든 환원 demonstration 가능성.  통일 안
되면 더 많은 axiom 필요 했을 것.

| 측면 | 양 |
|------|-----|
| Axiom clauses | 3 |
| External axioms | 0 |
| Generates | countable Raw structure |
| Lens views span | 1, ℕ, 𝔠, ... |
| Falsifying instances | 0 |

## 변경 이력

- 2026-04-25: 잔여물-생성 통일 의 명시 적 articulation.
