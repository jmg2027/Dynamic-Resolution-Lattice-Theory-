# Pivot Analysis: "≠" → "관계 존재"

**Question:** Thesis 의 primitive 를 "≠ (apartness)" 에서
"관계가 존재한다 (relation exists)" 로 변경 시 어떤가?

---

## 1. 두 Framing 의 형식 비교

### Framing A (기존): Apartness primitive

```
Axiom: x ≠ y → new object slash(x, y) exists.
```

문제:
- `≠ := (= → False)` linguistically 의존.
- Negative framing.
- Brouwer/Heyting 과 중복.

### Framing B (새): Relation existence primitive

```
Axiom: For any two objects x, y, relation rel(x, y) exists.
Constraint: rel(x, x) is degenerate (self-identity, no new info).
```

장점:
- Positive framing.
- Category theory 와 align.
- `=`, `≠` 둘 다 derived (relation 의 type).

---

## 2. Formal 동일성

**둘 다 formal 결과는 동일.**

Framing A 의 `slash x y h` = Framing B 의 `rel x y with x ≠ y`.
Raw 구조, Reachable, Lens, 모두 변경 없음.

**차이:** Narrative 와 axiom presentation 만.

---

## 3. Novel 관점 변화

### Framing A 의 novelty claim

"≠ is sole primitive" — 약함 (Brouwer overlap).

### Framing B 의 novelty claim

"Relation existence is primitive; identity (=) and apartness (≠)
are derived by relation type" — 더 강함.

이유:
- 기존 수학은 = primitive (ZFC, FOL).
- 213 에서 relation 자체가 primitive.
- = 는 `rel x x` (self-relation).
- ≠ 는 `rel x y with distinct x, y` (non-self).
- **둘 다 relation 의 특수 case.**

---

## 4. 기존 연구와의 비교

### Category theory

- Objects + Morphisms primitive.
- 213 의 "relation primitive" 와 흡사.
- 하지만 morphism 은 directed + composable.
- 213 의 rel 은 directed but pre-composable.

### Graph theory / Relation algebra

- Vertices + edges.
- 213 의 Raw atoms + rel 와 흡사.
- 이미 여러 세기 연구됨.

### Dependent type theory

- Types + inhabitants.
- 213 의 Raw + rel 이 구체 instance.

**결론:** "relation primitive" framing 도 기존 frameworks 와
overlap 있음. 완전 novel 아님.

---

## 5. 개선된 Novel Claims

"Relation 존재" framing 으로 narrow claims 재작성:

**N1'.** The 213 framework treats binary relation existence as
primitive, with:
  - identity = rel(x, x) (self-relation).
  - apartness = rel(x, y) with distinct x, y.
  Both equality notions emerge from a single primitive.

**N2'.** The antireflexive constraint (rel x x 이 new object 생성
안 함) 은 infinite generation 을 제어하면서도 self-identity 표현.

**N3'.** Lens framework 는 relation-primitive system 의 invariant
structures 를 체계화.

이건 기존 framing 보다 **positive + category-friendly**.

---

## 6. 권고

**Thesis 수정 방향:**

**Old:** "≠ is sole primitive; axiomatic systems are shadows of ≠."

**New:** "Binary relation existence is primitive; equality (=) and
apartness (≠) are relation-type specifications. The 213 framework
formalizes this with Lean 4 (0 sorry), instantiating 5 standard
systems via lens choice."

이게 더 defensible + positive.

---

## 7. 최종 평가

| 기준 | ≠-primitive | Relation-primitive |
|---|---|---|
| Linguistic robustness | ★★ | ★★★★ |
| Positive framing | ★★ | ★★★★ |
| Category theory fit | ★★★ | ★★★★ |
| Brouwer overlap | ★★★★ | ★★ |
| Formal substance | 동일 | 동일 |
| Novel (narrow) | 약함 | 약간 나음 |

**Recommendation:**
Relation-primitive framing 으로 pivot.
- Philosophy 더 자연스러움.
- 기존 분야 와 alignment 개선.
- Formal substance 는 변화 없음 (Raw framework 유지).

**주의:**
Novel contribution 의 substance 변화 없음.
여전히 real novel result:
- Lean formalization.
- R3 cardinality cliff.
- 5 system lens instances.

이 구체 results 는 어느 framing 이든 동일.
