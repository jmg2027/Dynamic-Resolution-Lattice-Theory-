# THESIS.md 재검토 (표준 수학자 관점)

**Verdict:** 주장 weakened 필요. 현재 claim 과중.

---

## 1. Thesis Claim 의 비판적 분석

### 1.1 "≠ is sole primitive" — 약점

**문제:** 213 의 slash 정의는 Lean 의 Eq primitive 에 의존.
```
slash (x y : Raw) (h : x ≠ y) : Raw
x ≠ y := x = y → False  (Lean definition)
```
⇒ `≠` 는 `=` 로 정의됨. `=` 없이는 `≠` 도 없음.

**결론:** "sole primitive" 는 linguistically false.
정확: "`≠` is foreground; `=` is hidden dependency."

### 1.2 "모든 공리계 = ≠ 의 그림자" — 약점

**반례 후보:**
- Higher-order logic (quantifier over predicates).
- Modal logic (possible worlds).
- Linear logic (resource-sensitive).
- Type theory (dependent types).

이들은 첫-order equality 외 추가 primitive 사용.
Lens framework 가 이들을 covered?
- Lens = Raw → α + combine.
- Raw 는 tree (HF-level).
- Higher-order, modal, linear 은 Raw 로 직접 encoding 어려움.

**결론:** Claim 3 의 "every S" 는 증명 없이 overreach.

### 1.3 Meta-theorem (Universal ≠-reduction) — 약점

현재 statement: "S with = is interpretable as lens L_S."
**Formal proof 부재.**
Lean 으로도 이 meta-theorem 자체 증명 안 됨.
→ Handwave.

실제 증명 가능한 것:
- 5 specific systems (Peano, Logic, Set, Topology, Algebra) 의 lens instance.
- 이건 "examples," 아닌 "universal theorem."

---

## 2. 기존 연구와의 실제 overlap

### 2.1 Apartness primitive 역사

- **Brouwer (1925):** apartness (#) in analysis.
- **Heyting (1930s):** constructive arithmetic.
- **Bishop (1967):** _Foundations of Constructive Analysis_.
- **Troelstra-van Dalen (1988):** _Constructivism in Mathematics_.

이들 이미 "apartness primitive" framework 확립.
213 의 ≠-primitive claim 은 **새롭지 않음**.

### 2.2 Categorical foundations

- **Lawvere-Rosebrugh:** sets-for-mathematics (kernel-based).
- **Algebra of programs (Bird, Meertens):** catamorphism.
- **Topos theory:** subobject classifier as primitive.

Lens framework 는 기존 이론의 재표현.

---

## 3. 진짜 Novel Contribution (narrow)

Thesis 를 realistic 하게 재작성:

### Narrower Novel Claims

**N1.** Lean 4 formalization of a 5-system lens-based hierarchy
  with 0 sorry across 66 files.
  - Status: True, verifiable.
  - Novelty: Moderate.

**N2.** Rule Hierarchy exhibits specific cardinality collapse:
  R3 (recursion) removal takes ℵ₀ to 12 in one step.
  - Status: Formally proven (Thm 15.5).
  - Novelty: Possibly new observation.

**N3.** Lens kernel as explicit invariant for 5 concrete systems.
  - Status: 5 concrete instances proven.
  - Novelty: Low (categorical folklore in new notation).

### 버려야 할 overreach

- "Sole primitive" — Lean 에서 ≠ 은 = 에 의존.
- "All axiomatic systems" — 5 examples ≠ universal theorem.
- "Shadows of ≠" — poetic, not formal.

---

## 4. 수정된 Thesis 권고

**Original:** "≠ is the sole primitive; existing axiomatic
systems are shadows."

**Revised:** "A finite-rule inductive type with antireflexive
binary relation can host lens-indexed interpretations of five
standard systems (Peano, propositional logic, naive finite set
theory, 3-point topology, Z/3Z). The 7-rule hierarchy exhibits
a cardinality cliff at recursion removal. All 120+ theorems
are Lean-verified (0 sorry)."

이게 defensible claim.

---

## 5. Publishable Strategy

### Paper 1 (ITP / CPP, 12-15 pages)

Title: "A Lean-verified lens-based framework for comparing
finite axiomatic systems."

Content:
- §1 Raw + slash.
- §2 Lens + kernel.
- §3 5 system instances.
- §4 Rule hierarchy cardinality.
- §5 Formalization statistics.

### Paper 2 (Philosophy of Math)

Title: "Apartness as foreground: a formal revisit of Brouwer's
primitive."

이건 philosophical, math content 약함.

---

## 6. Final Verdict

**현재 THESIS.md:**
- Claim over-reach.
- Brouwer 과 충분히 구별 안 됨.
- Meta-theorem formal proof 부재.
- Lean dependency 인정 부족.

**Recommendation:**
1. "Sole primitive" 삭제 or weakened.
2. "Shadows" 수사 삭제.
3. 5 concrete systems 으로 narrow.
4. Rule hierarchy cliff 를 main result.
5. Brouwer 역사 명시.

**수학자 평가:** 현재 form reject. Revised version 은 ITP/CPP
가능성 있음.
