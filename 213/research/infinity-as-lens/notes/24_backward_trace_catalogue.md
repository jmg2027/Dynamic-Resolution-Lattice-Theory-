# 24 — Backward trace catalogue: 여러 Lens 의 backward tree

## Purpose

Note 23 의 backward framework 를 구체 Lens 들에 적용.  각각
의 backward tree 가 어떤 모양인지, Raw 까지 몇 단계인지,
bootstrap 순환이 어디서 발생하는지 기록.

목표: **Lens 복잡도 = backward depth** 인지 확인 + Raw 에
가장 가까운 "원형 Lens" 가 무엇인지 식별.

---

## §1. 방법론

각 Lens L = (α, base_a, base_b, combine) 에 대해:

1. α 의 backward trace (어떤 Lens 의 image).
2. base_a, base_b 의 backward trace (α 내 원소 선택).
3. combine 의 backward trace (α 위 연산).
4. 최심 기록 — Raw 또는 bootstrap loop 까지 단계 수.

---

## §2. `Lens.leaves` — Nat-Lens 원형

```
Lens.leaves = (Nat, 1, 1, +)
 ├─ Nat : Raw 의 counting 결과 (Raw.fold 기반)
 │   → bootstrap loop 발견 (note 23 §3).
 ├─ 1 : Nat.succ Nat.zero — Nat 내부.
 ├─ + : Nat.add — Nat 내부.
```

**backward depth**: 2 (Lens → Nat → Raw/bootstrap).

**bootstrap**: Nat 을 만드는 Lens 가 Nat 을 쓴다.  **자기참조
fixed point**.

---

## §3. `Lens.depth` — leaves 와 같은 구조, 다른 상수

```
Lens.depth = (Nat, 0, 0, λ a b => 1 + max a b)
 ├─ Nat : bootstrap loop (leaves 와 동일).
 ├─ 0 : Nat.zero.
 ├─ max : Nat ordering 필요 → Nat 내부.
 ├─ + : Nat.add.
```

**backward depth**: 2.

**관찰**: leaves 와 depth 는 **같은 backward tree** 를 가짐.
오직 base 값 (1,1 vs 0,0) 과 combine (+ vs 1+max) 만 다름.

**함의**: backward tree 의 **뼈대** (α + 필요 연산 종류) 가
Lens 의 "형태" 를 결정.  base 값과 특정 combine 은 그 뼈대
안의 "파라미터" 선택.

---

## §4. `signedLens` — Int 를 거침

```
signedLens = (Int, 1, -1, +)
 ├─ Int : Lean 에서 Int = ℕ ⊕ ℕ (부호 + 자연수) 구조.
 │   → Int → Nat → bootstrap.
 ├─ 1 : Int.ofNat 1 — Nat 의존.
 ├─ -1 : Int.neg 1 — Int.neg 연산 의존.
 ├─ + : Int.add.
```

**backward depth**: 3 (Lens → Int → Nat → bootstrap).

**추가 요소**: `Int.neg` 는 Nat 에 없는 연산.  즉 Int 는 Nat
에 **음수화 Lens** 를 하나 더 얹은 것.

**함의**: signedLens 는 Nat-Lens 원형 위에 **involution
(음수화) Lens** 가 쌓인 구조.

---

## §5. `parityLens` — Bool: 최단 체인

```
parityLens = (Bool, false, true, xor)
 ├─ Bool : 2-원소 타입.  Raw 의 2 원시 구분 (a, b) 의 직접
 │   매핑.  a ↦ false, b ↦ true.
 │   즉 Bool = Raw 의 **원시 구분 Lens** 의 image.
 │   → bootstrap 없음!
 ├─ false, true : Bool 의 두 구성자.  Raw.a, Raw.b 와 1:1.
 ├─ xor : Bool 위 이항.  Raw.slash 와 유사하지만 다름 —
 │   xor 은 x ⊕ x = 0 로 collapse; slash 는 x ≠ x 면 정의
 │   안 됨 (anti-reflexive).
```

**backward depth**: **1** (Lens → Bool → Raw 직접).

**핵심 관찰**: Bool 은 Raw 의 **가장 얇은 Lens 이미지** —
"2 원시 구분" 만 Lens 로 수송.  연산은 따로.

**bootstrap 없음**: Bool 은 Nat 보다 원시적 (2-element
만 필요, counting 불필요).  Nat-bootstrap 을 거치지 않음.

**함의**: **Bool 은 Raw 의 "거울" 같은 Lens**.  backward
체인이 짧은 Lens 일수록 Raw 에 가까움.

---

## §6. K_n Lens (complete graph)

```
K_n Lens = ?
 ├─ K_n : 완전그래프 on n vertices.  n 필요 → Nat 의존.
 │   → backward: K_n → Nat → bootstrap.
 ├─ Vertex/edge 구분 : Bool-like.
 ├─ Edge weight : DRLT 에서 ℂ.  ℂ → ℝ → Cauchy → Nat.
```

**backward depth**: 3–5 (edge weight 포함 시 ℂ → ℝ →
Cauchy 완비 → Nat bootstrap).

**함의**: K_n 은 Bool, Nat, Int, ℝ, ℂ 를 **모두 경유**하는
합성 Lens.  backward tree 가 넓고 깊음.  실용적 Lens 중
가장 풍부 (note 18 의 visual intuition).

---

## §7. 복잡도 표 — Backward depth 가 측정하는 것

| Lens          | Codomain | Backward depth | Bootstrap? |
|---------------|----------|----------------|------------|
| parityLens    | Bool     | **1**          | 없음       |
| boolAndLens   | Bool     | 1              | 없음       |
| Lens.leaves   | Nat      | 2              | Nat        |
| Lens.depth    | Nat      | 2              | Nat        |
| maxLens       | Nat      | 2              | Nat        |
| signedLens    | Int      | 3              | Nat        |
| zmod6Lens     | Nat      | 2              | Nat        |
| pathLens      | List Bool| 2              | Bool (없음) + List (Nat) |
| K_n Lens      | K_n      | 3              | Nat        |
| DRLT G_ij     | ℂ (matrix) | 5+           | Nat (여러 층) |

**관찰**:

1. **Bool 이 근원**.  backward depth = 1.  Raw 와 직접 인접.
2. **Nat 이 첫 bootstrap 지점**.  depth 2 Lens 들 다수.
3. **Int, List, Matrix 등은 Nat 위 layering**.
4. **ℂ 는 가장 깊은 tower 정상**.  DRLT 가 ℂ 를 쓰는 건
   "가장 풍부한 Lens" 를 쓴다는 뜻.

---

## §8. 핵심 발견: 두 종류의 Lens

Backward 관점에서 Lens 는 두 부류로 나뉜다:

**(i) bootstrap-없는 Lens**
- Bool-valued: parityLens, boolAndLens, boolOrLens, boolXorLens.
- Backward depth = 1.
- 순수히 "Raw 의 2 원시 구분" 만 관측.
- **Raw 의 원형 Lens**.

**(ii) bootstrap-있는 Lens**
- Nat-valued 이상: leaves, depth, signed, ..., DRLT G_ij.
- Backward depth ≥ 2.
- Nat-bootstrap 을 반드시 거침.
- **self-reference fixed point 를 경유**.

**추측**: **모든 bootstrap-있는 Lens 는 self-reference 고정점
을 경유한다**.  이 고정점이 Nat 의 정체성 자체.

---

## §9. 다음 단계

- (b) Lean 형식화 시도 — `Research/BootstrapWitness.lean`.
  Nat-bootstrap 이 Lean type theory 에서 어떻게 처리되는가
  명시 확인.
- 추가 Lens backward trace (Cayley, Lipschitz, Sedenion).
- "Bool-Lens = Raw 원형" 가설의 Lean 형식화.

## 변경 이력

- 2026-04-24: 최초 작성.  Note 23 의 framework 를 catalogue.
