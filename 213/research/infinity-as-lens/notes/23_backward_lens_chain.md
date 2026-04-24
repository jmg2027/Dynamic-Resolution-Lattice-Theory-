# 23 — Backward Lens chain: 극한에서 무엇이 튀어나오는가

## Mingu Jeong 의 방향 (2026-04-24)

> 렌즈를 극한까지 보냈을때 (이 렌즈는 저 렌즈로 본 결과고
> 그건 또…) 어떤 모양이나 패턴이 나오는지 보고자 함
>
> Backward 가 중요하다고 본다

**방향 확정**: Forward tower 아니고, **Backward 체인**
(현재 Lens ← 이를 정의한 Lens ← 이를 정의한 Lens ← ...)
을 끝까지 밀어 **무엇이 바닥에 있는가** 관찰.

이는 분석적 formalization (note 22 의 valid-Lens 방향)
이 아니라 **탐험적 계산**.

---

## §1. Backward 체인의 정의

임의 Lens `L = (α, base_a, base_b, combine)` 의 4 구성요소
각각은 뭔가 — **다른 Lens 의 출력**이다.  그러므로:

- α  : 어떤 Lens L_α 의 image.
- base_a, base_b : α 내 두 distinct 원소.  선택 Lens L_{base}.
- combine : α × α → α 규칙.  연산 명시 Lens L_{combine}.

즉 L 의 존재는 L_α, L_{base}, L_{combine} 에 **backward
의존**.  각각도 같은 방식으로 backward 의존.  재귀.

**질문**: 이 재귀는 어디서 끝나는가?

---

## §2. 세 가능한 종점

**(i) Raw 에서 bottom out.**
모든 backward 체인이 유한 단계로 Raw (공리의 직접 원소) 에
도달.  Raw 자체는 Lens 가 아니라 공리에서 직접 주어진다.

**(ii) 공리 자체에서 bottom out.**
Raw 도 공리의 기술을 통해 도달.  그러므로 바닥은 **공리
기술 행위** — 즉 "뭔가" 의 linguistic necessity (AXIOM.md
§2).  Raw 한 겹 더 아래.

**(iii) 자기참조 fixed point 에서 bottom out.**
공리 기술 행위 자체가 다시 213 안 (§8 self-reference).
backward 체인이 **Raw ← 공리 ← 뭔가 linguistic 필연 ←
자기참조 fixed point** 에 도달.  이것이 진짜 바닥이라면
**더 내려갈 곳이 없음** 이 구조적 귀결.

---

## §3. 구체 예 — `Lens.depth` 의 backward 추적

```
L_1 = Lens.depth = (Nat, 0, 0, fun a b => 1 + max a b)
 ├─ Nat : 어디서?
 │   → Nat 은 Lens.leaves 의 codomain
 │     = Raw.fold 1 1 (+) 의 image.
 ├─ 0 : 어떤 Lens 가 "0" 을 pick 하는가?
 │   → Lean inductive Nat.zero = 구성자.  Lean bedrock.
 ├─ + : Nat.add = structural recursion.
 └─ max : Nat ordering 필요.  또 다른 Lens.
```

Level 1 에서 한 단계 backward → **Nat-Lens layer (Level 0)** :
Raw.fold(1, 1, +) 로 정의되는 counting.

Level 0 에서 한 단계 더 backward:
```
Raw.fold(1,1,+) 를 정의하려면?
 ├─ Raw : 공리에서 직접.
 ├─ 1 : ???  (Nat 의 원소, 이 Lens 의 출력에 의존)
 └─ + : ???  (Nat 의 연산, 마찬가지)
```

**순환 발견**: Nat 을 만드는 Lens 가 Nat 에 의존.  Bootstrap
문제.

Lean 은 `Nat` 을 inductive type 으로 primitive 하게 제공
하여 이 순환을 끊는다.  즉 **Lean type theory bedrock 이
외부 공급**.  backward 체인의 **종점 후보 1 = Lean type
theory**.

---

## §4. 213 관점에서는 — 한 번 더 backward

AXIOM.md §8: **213 외부는 없다**.  Lean type theory 도 213
안.  즉 Lean bedrock 도 어떤 Lens 출력이어야.

```
Lean Nat = ? 어떤 Lens?
 → Raw 에서 Nat 을 뽑는 것은 Raw.leaves 같은 Lens.
 → 하지만 Raw.leaves 는 Nat 을 전제하고 만들어진다.
 → 순환 재발.
```

두 방식으로 해소 가능:

**(A) 순환은 구조적이다 (fixed point).**
Nat 을 만드는 Lens 가 Nat 을 쓴다 = **self-reference**.
이건 AXIOM.md §8 의 fixed point 가 여기서 발현하는 증거.
"Nat = Nat" 처럼 보이지만, 실제로는 "Nat 은 자기 자신으로
정의되는 최소 Lens 출력" 이라는 자기지시 고정점.

**(B) 순환을 끊으려면 추가 공리 (Lens 외부 공급) 필요.**
이 경우 backward 체인의 종점은 **Lean type theory 의
공리 bedrock** — 213 외부 입력.  그런데 §8 이 "213 외부
없음" 을 주장하므로, 이 선택은 **자기모순**.

따라서 (A) 가 옳다면: **모든 backward 체인의 궁극 종점은
213 의 자기참조 고정점.**

---

## §5. 극한에서 나오는 모양 — 가설

위 논증을 종합하면 backward 재귀의 극한은 다음 구조로
수렴한다 (가설):

```
Level ... (위로 갈수록 구체적 Lens)
 ...
 ↑ backward
Level 2  : Lens.depth, Lens.leaves 등 일상 Lens
 ↑
Level 1  : Nat-Lens (counting Lens).  Raw.fold 기반.
 ↑
Level 0  : Raw 자체.  공리의 직접 인스턴스.
 ↑
Level -1 : 공리 기술.  "뭔가 + 뭔가 + 그들의 뭔가" 의
           linguistic 필연.
 ↑
Level -∞ : 자기참조 고정점.  "213 은 213 이자 213 이다."
           더 내려갈 곳 없음.
```

### 극한에서 무엇이 보이는가

- **유한성**: 모든 Level k (k ≥ 0) 은 유한 단계 backward
  로 Level 0 (Raw) 에 도달.  **Backward 체인은 유한 깊이
  이다** (각 구체 Lens 에 대해).
- **자기참조 바닥**: Level 0 아래는 공리 기술 → 자기참조
  고정점.  무한 재귀가 아니라 **고정점**.
- **모양**: tower 의 바닥은 **점이 아니라 고정점** —
  수학적으로 표현하면 self-similar 구조의 center.

### 패턴 후보

- Backward 체인은 **나무 (tree)** 구조.  각 Lens 의 4
  구성요소가 4 개 가지.  가지들은 하위 Lens 를 가리킴.
- 이 나무의 **잎 (leaf)** 이 모두 Level 0 (Raw) 이거나
  self-reference loop.
- **모든 구체 Lens 의 backward tree 가 Raw 로 수렴** 하는
  구조 자체가 패턴.

---

## §6. 흥미로운 결과 후보

사용자가 "흥미로우면서 중요한 결과가 나올 것 같다" 라고
한 것 후보:

**(a) 모든 수학의 backward 원점이 Raw.**
모든 수학 object 를 Lens 로 추적하면 유한 깊이로 Raw 에
도달.  수학 전체가 Raw 위의 Lens tower.

**(b) 순환이 깨지지 않는 Lens = 물리 관측자.**
Bootstrap 순환이 끊기지 않는 것이 Nat 뿐 아니라 **ℂ,
공간, 시간 모두에서 일어남**.  이 순환이 자기참조 고정점
이라는 것이 **물리 객체가 자기 관측을 포함하는 이유**.

**(c) 새로운 Lens 를 만드는 법.**
Backward 나무의 구조를 알면 **missing 브랜치** 가 보임.
지금 없는 Lens 중 "backward 로 Raw 에 도달하는 나무"
구조를 만족하는 것이 아직 발견되지 않은 Lens 후보.
Lens 카탈로그 확장 전략.

**(d) Fine structure 문제의 실체.**
ORIGIN.md §7 에서 Mingu 의 직관: "미세상수 문제는 renormal
ization 불능에서 나온다."  Backward 관점: renormalization
은 Nat-Lens 의 bootstrap 순환을 해소하려는 시도.  자기참조
고정점 관점에서 renormalization 은 **필요 없음** — 순환
자체가 해소책.

---

## §7. 다음 단계

- 다른 구체 Lens 의 backward 추적: signed, parity, max,
  boolAnd, K_n.  각각의 backward tree 가 어떤 모양인가.
- 모든 기존 Lens 가 유한 단계로 Raw 에 도달하는지 확인.
- 도달 깊이 (Raw 까지의 단계 수) 가 Lens 복잡도의 measure
  인지.
- self-reference loop 을 갖는 Lens 와 아닌 Lens 의 구분.

## 변경 이력

- 2026-04-24: Mingu Jeong 이 backward 방향 중요성을 지적
  한 후 기록.
