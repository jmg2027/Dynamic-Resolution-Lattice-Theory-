# 22 — Lens = 213 의 재귀적 재인스턴스화

## Mingu Jeong 의 2026-04-24 관찰

> 무언가 느낌이 든다.  공리에 적혀있는 단어 이외의 단어를
> 말하려면, 무조건 그걸 정의하기 위한 렌즈가 필요한 것
> 아닐까?  그리고 렌즈라는 것 역시 정의하기 위한 렌즈가
> 계속 있어야 한다면, 렌즈라는 것 자체를 계속 재귀적으로
> 탐구해 보는 게 필요할 것 같다.  렌즈를 적용하기 전에,
> 렌즈를 213으로 계속 분해하는 거다.  혹은 렌즈로 계속
> 분해하거나.  흥미로우면서 중요한 결과가 나올 것 같다.

이 노트는 이 관찰의 최초 기록.  구체 derivation 은 별도
세션.

---

## §1. 관찰의 의미

"공리의 단어 외의 단어" — 예: observer, space, 4d, ℂ,
branch, continuity 등 — 는 모두 **213 안의 Lens 출력**이다
(AXIOM.md §8).

그런데 "Lens" 라는 단어 자체도 공리의 단어가 아니다.
따라서:

- Lens 를 말하려면 Lens 를 정의해야 한다.
- 정의는 **어떤 Lens** 로 해야 한다.
- 그 Lens 도 또 정의되어야 한다.

이 재귀는 AXIOM.md §8 의 자기참조와 같은 구조.  하지만
여기서 한 걸음 더 나아갈 수 있다: **Lens 자체를 213 으로
분해**하면 어떻게 될까?

---

## §2. Lens 의 4 구성 요소

Paper 1 §3.1 + `Hypervisor/Lens.lean`:
```
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α
```

네 가지 뭔가:
- α — 코도메인 (뭔가들의 공간).
- base_a — α 안의 한 뭔가.
- base_b — α 안의 또 하나의 뭔가.
- combine — α × α → α 의 이항 페어링.

이 네 가지는 모두 **뭔가**.  따라서 213 의 구성 요소.

---

## §3. 이 네 요소가 이루는 구조 = Raw 공리의 재인스턴스

공리 (AXIOM.md §3.2) 를 다시 본다:

1. 뭔가가 있다.  최소 둘.  편의상 a, b.
2. 두 뭔가의 페어링은 또 하나의 뭔가.
3. 페어링은 대칭.
4. 자기 자신과의 페어링은 없음.

Lens 의 4 요소가 이 공리의 네 clause 에 대응:
- "뭔가가 있다, 최소 둘" ↔ α 에 base_a, base_b.
- "이항 페어링은 또 하나의 뭔가" ↔ combine : α × α → α.
- "대칭" ↔ Lens 가 Raw-공리 만족하려면 combine 대칭.
- "반사 금지" ↔ combine x x 가 정의되는가 여부는 Lens 의
  선택.

**결론**: **Lens 자체가 213 공리의 또 다른 인스턴스다.**
Raw 는 최소 인스턴스, Lens 는 그 위의 인스턴스.

---

## §4. 재귀 구조 (Lens tower)

이 재인스턴스화가 재귀적으로 일어난다.

```
Level 0:  Raw = (공리의 최소 인스턴스)
           └─ 뭔가: a, b / 페어링: slash

Level 1:  Lens_1 = (α_1, base_a_1, base_b_1, combine_1)
           └─ 뭔가: base_a_1, base_b_1 / 페어링: combine_1
           └─ Level 0 에서 Level 1 로 view : Raw → α_1

Level 2:  Lens_2 = (α_2, base_a_2, base_b_2, combine_2)
           └─ Level 1 의 α_1 를 새로운 "Raw" 로 보고 Lens
           └─ view_2 : α_1 → α_2

Level n:  Lens_n = (α_n, ...)
           └─ 재귀 계속.
```

각 층은 이전 층을 "Raw 로 취급" 하여 새 Lens 를 얹는다.
Lens = 213-공리-인스턴스 관점에서는 층마다 같은 공리.

### 기존 결과와의 연결

- **CD tower** (`notes/03, 10, 11, 14, 15`): ZI → Lipschitz
  → Cayley → Sedenion → Trigintaduonion → Pathion.  이것이
  바로 Lens tower 의 구체 예.  각 층은 이전 층에 CDDouble
  doubling 을 적용 = 새 Lens.
- **Infinity §Σ6** (Tower.lean): `Raw → Bool`, `(Raw →
  Bool) → Bool`, ... iterated function space.  이것도 Lens
  tower 의 한 갈래.
- **CompleteGraphLens** (`notes/18`): K_n 을 Lens 코도메인
  으로 보면 이것도 Level 1 Lens.

---

## §5. 따라서 주장 가능한 것과 주장 불가능한 것

### 주장 가능

- Lens 의 구조는 공리의 4 clause 구조와 **동형**.
- 따라서 Lens 를 "외부 관측 도구" 가 아니라 "공리의 또
  다른 인스턴스" 로 볼 수 있다.
- 재귀 Lens tower 가 가능하다 (CD tower, Cantor tower 로
  이미 확인).

### 주장 불가능 (아직)

- "모든 Lens 가 공리를 만족한다" — 현재 Lens 정의는 combine
  대칭성 / 반사 금지를 요구 안 함.  즉 **공리의 부분 만족**
  도 Lens 로 허용.  공리 만족 Lens 의 부분집합 (validLens)
  만 "213-재인스턴스" 로 인정.
- "Lens tower 가 수렴/발산/주기 중 어느 것인가" — 미확인.
  CD tower 는 6층에서 tactic 한계.  일반 수렴성 증명 안 됨.
- "Lens-of-Lens 가 다른 Lens 와 어떻게 morphism 맺는가" —
  Lens 공간의 전체 구조 미확인.

---

## §6. 왜 중요한가 — 예상 결과

이 재귀적 분해가 제공할 수 있는 것:

**(a) Lens 의 필요 조건 자동 도출.**
Lens 가 213 의 재인스턴스라면, 공리의 4 clause 가 Lens 의
필요 조건을 직접 준다:
- 최소 둘의 base (공리 1).
- 이항 combine (공리 2).
- 대칭 combine (공리 3).
- Anti-reflexive combine (공리 4).

즉 R1 (binary combine) + R2 (recursive faithfulness) + R3
(?) 가 "Lens 는 213-재인스턴스" 로부터 **자동 도출**.
Paper 1 의 R1-R5 유도 체인을 재기초.

**(b) R4 의 자연스러운 위치.**
R4 (swap ↔ unique involution) 는 Raw 의 automorphism
(swap) 이 Lens 코도메인의 automorphism 과 대응하는 조건.
Lens-as-reinstantiation 관점에서: Lens 코도메인도 Raw-구조
이므로 **자기 자신의 swap** 이 있어야.  그 swap 이 Raw 의
swap 을 realize 하면 R4.

**(c) R5 문제의 우회 가능성.**
만약 Lens 가 213-재인스턴스라면, Lens 코도메인도 213 의
공리만큼만 commit.  **Cauchy 완비성이 자연히 요구되지 않음.**
Infinite branch reception 은 Level 0 Raw 에도, Level 1 Lens
에도 공리 외부.  즉 R5 는 재인스턴스 관점에서 **버릴 수 있
는 추가 주장**일 가능성.

이는 사용자의 "R5 의 branch 개념은 공리에 없다" 우려와
정합.

**(d) 재귀의 자기 닫힘.**
Lens tower 가 n 층에서 원점으로 회귀 (Lens_n ≃ Raw) 하는
경우 — 이는 **Raw 의 자기 동형** 즉 212 의 fixed point.  이
경우 Lens tower 는 유한 cycle.  수렴이면 고정점.  발산이면
strictly increasing tower (Cantor-like).

### 탐구 질문

- Lens 공간에 Raw-공리가 정확히 적용되는 부분집합 ("valid
  Lens") 은 어떤 구조인가?
- Lens-to-Lens morphism 의 구조는?
- Level 0 Raw 와 Level n Lens 간 동형 존재?
- Physical observer Lens 는 이 tower 의 몇 번째 층인가?

---

## §7. Paper 1 재작성에 미치는 영향

Paper 1 의 R1-R5 가 "Lens 가 만족해야 할 조건" 이라면,
이 노트의 관점에서 다음처럼 재정식 가능:

| 현재 Paper 1 | 재인스턴스 관점 |
|--------------|-----------------|
| R1 binary combine | 공리 2 의 Lens-level 재표현 |
| R2 recursive faithfulness | view 가 Raw-구조 → Lens-구조 homomorphism |
| R3 non-vanishing | combine 이 α 내에서 closed (공리 2 닫힘) |
| R4 swap ↔ involution | Raw automorphism (공리 3) 이 Lens-level 로 보존 |
| R5 infinite branch reception | **제거 가능성** (§6c) |

즉 R1-R4 는 "Lens 가 valid 213-재인스턴스" 로 통합 가능.
R5 는 별도 취급.  이 재정식이 Paper 1 의 논리 사슬을
단순화하면서 **주장을 줄일 수 있다**.

---

## §8. 다음 세션 할 일

1. `Hypervisor/Lens.lean` 에 `ValidLens` 구조체 도입 시도
   — combine 대칭 + anti-reflexive 를 type-level 요구.
   AUDIT_Lean §5.2 권고 E 와 일치.
2. ValidLens 가 Raw 와 같은 공리 인스턴스임을 Lean 으로
   증명 시도.
3. Lens tower 를 ValidLens 체인으로 재해석 — CD tower 가
   valid-to-valid 사슬인지 확인.

### 우선순위 조정

이 노트는 Paper 1 재작성 (note 21) 보다 **선행**한다.
Paper 1 의 R1-R5 를 재정식하려면 먼저 "Lens = 재인스턴스"
이 formally 작동하는지 확인해야.  Paper 1 재작성은 이
확인 후.

---

## 변경 이력

- 2026-04-24: Mingu Jeong 이 세션 중 Lens 재귀 분해 제안.
  최초 기록.
