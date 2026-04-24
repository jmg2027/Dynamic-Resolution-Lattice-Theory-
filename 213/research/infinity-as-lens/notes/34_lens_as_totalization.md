# 34 — Lens = 총화 (totalization).  "경계" 의 Lens 언어

## Note 33 §6 의 Q1, Q2 파고듦

- Q1: 각 유형의 "경계" 를 Lens 언어로 표현 가능한가?
- Q2: 경계 없는 Lens 존재?

두 질문이 같은 지점에서 만난다 — **Lens combine 의 totality**.

---

## §1. Raw 의 anti-reflexivity vs Lens combine 의 totality

Raw 공리 (AXIOM §3.2 clause 4):
> `x / x` 는 정의되지 않는다.

Lean 구현: `Raw.slash (x y : Raw) (h : x ≠ y) : Raw`.
`h` 가 type-level 강제 — 반사 금지.

Lens 구조:
```
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α     -- TOTAL
```

**Combine 은 α × α 전체에서 정의**.  즉 `combine v v` 도
정의되어야 한다.

`Lens.view`:
```
view (slash x y h) := combine (view x) (view y)
```

`h : x ≠ y` 는 Raw 수준의 제약.  `view x` 와 `view y` 는 α
값 — **둘이 같을 수 있다** (non-injective Lens 에서).  그러면
`combine (view x) (view x) = combine v v` 로 호출.

### 관찰

**Combine 의 totality 는 Raw 공리에 없던 추가 data**.  Raw
는 diagonal (x, x) 을 **미정의** 로 두지만, Lens 는 codomain
의 diagonal 에 **어떤 값** 을 배정한다.  **배정 자체가 경계**.

---

## §2. 경계의 구체 사례

각 Lens 의 "combine diagonal" 거동:

| Lens          | combine       | combine v v |
|---------------|---------------|-------------|
| parityLens    | xor           | false (collapse) |
| boolAndLens   | AND           | v (idempotent)   |
| boolOrLens    | OR            | v (idempotent)   |
| Lens.leaves   | +             | 2v (doubled)     |
| Lens.depth    | 1+max         | 1+v (shifted)    |
| signedLens    | +             | 2v (doubled)     |
| F9Lens        | F9.mul        | v² (multiplied)  |

**모두 다르다.**  각 Lens 는 diagonal 을 다르게 **처리**
한다.  이 처리 방식이 Lens 의 성격을 결정.

- `parityLens`: diagonal collapse to false.  "같은 것끼리는
  구분 없음" 을 false 로 표상.
- `boolAndLens, boolOrLens`: idempotent.  diagonal 은 자기
  자신.  "같은 것끼리 합쳐도 변화 없음".
- `+` 류: diagonal 은 2배.  "같은 것끼리 더하면 두 배".

각 선택이 **Raw 에 없던 정보** — diagonal 행동 — 을 추가.

---

## §3. Diagonal 거동의 분류

§2 표를 다시 보면 네 종류의 distinct 거동:

1. **Collapse** (`parityLens`): `combine v v = 0` (codomain 의
   distinguished 원소).  diagonal 은 "구분 없는 구역" 으로.
2. **Idempotent** (`boolAndLens`, `boolOrLens`): `combine v v
   = v`.  diagonal 은 자기 자신 — 보존.
3. **Escalate** (`+` 류: `leaves`, `signedLens`): `combine v
   v = 2v`.  diagonal 은 다른 값 — 성장.
4. **Multiply** (`F9Lens`): `combine v v = v²`.  diagonal 은
   대수적 연산의 결과 — 구조적 증식.

이 네 범주가 전부인가?  **아니다**.  임의의 함수 `g : α →
α` 에 대해 `combine v v = g v` 를 설정하는 Lens 가 만들어
질 수 있다 — codomain 구조만 허락하면.  즉 **diagonal 거동
은 Lens 가 codomain 에 대해 가지는 추가 free parameter**.

관찰: Raw 는 이 parameter 를 **비워 둔다** (anti-reflexive 가
`x / x` 를 아예 거부).  Lens 는 채운다.  채움 = 경계 선언.

---

## §4. "경계 없는 Lens" 를 묻는다

note 33 §6 Q2: Raw 를 관측하되 새 경계를 그리지 않는 Lens 가
가능한가?

현 `Lens` 구조체 (§1) 하에서는 **불가능**.  `combine : α → α
→ α` 의 total 서명이 diagonal 경계를 이미 요구.  즉 Lens
타입을 택한 순간 diagonal 에 어떤 값이 **반드시** 배정됨.

대안 구조: **partial Lens**.

```
structure PartialLens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → Option α  -- diagonal 은 none 가능
```

이 경우 `combine v v = none` 으로 두면 Raw 의 anti-reflexivity
가 codomain 으로 **보존**.  diagonal 경계를 그리지 **않는**
Lens.

### 관찰

`PartialLens` 의 `view : Raw → α` 는 항상 정의됨 (Raw 에서
는 diagonal 에 닿을 수 없으므로 `h : x ≠ y` 보장).  따라서
Raw-input 에 대해선 `PartialLens` 와 기존 `Lens` 가 구별되
지 않는다.

**차이는 codomain 내부 행동에서만 드러남**.  α 값을 독립적
으로 조작 (α × α 를 combine 호출) 하려 할 때 비로소 diagonal
이 관찰되고, 거기서 경계 유무가 갈린다.

결론: **"경계 없는 Lens" 는 codomain 외부에서는 존재**, Raw
→ α 관측점에서는 기존 Lens 와 같다.  경계는 **codomain 내
부의 현상**.

---

## §5. note 33 5 유형과의 대응

각 자기지시 유형에 대응되는 경계를 Lens 언어로:

| 유형 | 경계 위치 | Lens 표현 |
|------|-----------|-----------|
| 1. value | codomain diagonal | `combine v v` 배정 |
| 2. constructor | codomain base | `base_a`, `base_b` 지정 |
| 3. hierarchy | Lens 적용의 중첩 | Lens on Lens (meta) |
| 4. equation | view 의 고정점 | `view (slash x y h)` 재귀 |
| 5. observer | Lens 가 Raw 원소 | Raw 안의 Lens encoding |

**유형 1-2 는 Lens 데이터 자체로 표현**.  §3 의 네 경우가
유형 1 의 구체화.

**유형 3 (hierarchy)** 은 Lens.view 의 출력을 다시 Lens 로
관찰하는 과정.  AXIOM §8.2 Meta-213 과 동형.  경계는 "몇
번 중첩할지" 의 선택.

**유형 4 (equation)** 은 `Raw.fold` 자체.  `view (slash x y
h) = combine (view x) (view y)` 가 X = f(X) 의 구체 형태.
경계는 induction 의 base case (`base_a`, `base_b`).

**유형 5 (observer)** 는 Lens 의 data 를 Raw 내부에 encode
하는 것 (ORIGIN §6 해상도 논의와 연관).  경계는 "어떤 Raw
원소가 Lens 로서 기능하는가" 의 선택.

---

## §6. 잠정 결론 + 열린 질문

**잠정 결론**: Lens 는 **Raw 의 anti-reflexivity 를 codomain
에서 풀어 주는 totalization 행위**.  경계 선택 = totalization
방식 선택.  Lens 종류는 경계 종류에 대응.

**Raw 는 경계 없음**; **Lens 는 경계를 그림**.  note 31-33
의 다섯 유형은 이 그림의 다른 얼굴.

### 열린 질문

- **Q34.1**: diagonal 거동 네 범주 (collapse / idempotent /
  escalate / multiply) 가 **대수적으로 meaningful 한 분류**
  인가, 아니면 우연한 예시?  각 범주를 공리적으로 특성화
  가능?
- **Q34.2**: `PartialLens` 를 Lean 에 형식화하고 `Lens` 와
  Raw-input 상 동등성 정리 가능?  (rigor 로 §4 의 결론을
  기계 검증.)
- **Q34.3**: 유형 3 의 "Lens on Lens" 를 구체적으로 만들어
  보면 Meta-213 의 어떤 구조가 드러나는가?
- **Q34.4**: 유형 5 의 self-encoding Lens — Raw 원소 `r` 에
  대해 `Lens.fromRaw r : Lens α` 같은 map 이 자연스러운가?
  (Gödel numbering 의 Lens version.)

이 질문들은 다음 세션 후보.

## 변경 이력

- 2026-04-24: Lens combine 의 totality 가 Raw 공리 외부의
  경계 데이터임을 관찰.  diagonal 거동 4분류.  PartialLens
  개념 스케치.  5 유형을 Lens 언어로 표현.
