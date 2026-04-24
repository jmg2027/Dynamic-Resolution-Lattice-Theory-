# 43 — leaf vs slash: 관측 가능성의 비대칭

## 발견

Raw 의 **leaf 와 slash 는 Lens-관측 측면에서 비대칭**:

- **Leaf** (Raw.a, Raw.b) 의 characteristic function 은
  **Lens-expressible** (`Research/RawACharLens.lean`).
- **Specific slash** (e.g., slash(a, b)) 의 characteristic 은
  **Lens-expressible 아님** (`Research/SlashCharNotFold.lean`).

## §1. Leaf 쪽 (positive)

`rawACharLens : Lens Bool` 로 `view r = decide (r = Raw.a)` 실현.

구현: base_a = true, base_b = false, combine = const false.

이유: Raw.a 는 leaf — base 분기에서 직접 인식.  slash 분기는
자동으로 false (slash ≠ leaf).  단순 fold-structure.

## §2. Slash 쪽 (negative)

`slashCharFn r := decide (r = slash(a,b))` 는 fold-structured
아님.

이유: c(false, false) 가 **slash(a,b) 를 포함하는 경우**에는
true 여야 하고, **다른 경우**에는 false 여야 함.  fold 는
(view x, view y) 만 보므로 구분 불가 → 모순.

## §3. 구조적 의미

Raw 의 내부 비대칭:
- Leaf = "더 이상 나눠지지 않는 원소" — 하나의 atomic identifier.
- Slash = "compositional 결과" — 구조를 **통해서만** 정의됨.

Lens 의 관측 방식:
- fold-structured — bottom-up.
- Leaf 는 fold 의 base 에서 직접 관측.
- Slash 는 view x, view y 의 combine 으로만 보임 —
  **자기 자신의 structure 는 view 에 없음**.

귀결: **Lens 는 slash 의 specific identity 를 관측 못 한다**.
"이것이 특정 slash A/B 인가?" 같은 질문은 Raw-level 질문이지
Lens-level 이 아님.

## §4. 철학적 함의

이 비대칭은 "관측자" 와 "관측 대상" 의 관계에 대한 깊은
observation:

- 관측자 (Lens) 는 **fold-compositional** (bottom-up combine).
- 관측 대상 (Raw) 은 **structural** (top-down nested).

관측자가 자기 방식으로 관측 대상을 **완전히 재구성** 할 수
없음.  **어떤 구조적 정보는 관측에서 빠짐**.

이는 양자역학의 "관측이 대상 정보를 완전히 포착 못 함" 의
213-내부 analog.  공리에서 직접 derive 되는 structural
observation 이지 형이상학 주장 아님.

## §5. Lens-관측 가능 원소의 범위

위 결과의 일반화:

| 원소 | Lens 로 characteristic 표현? |
|------|------------------------------|
| Raw.a | ✓ |
| Raw.b | ✓ |
| specific slash r | ✗ |

Lens 는 **leaf identity** 는 추출 가능하지만, **slash identity**
는 불가능.  Raw 구조의 원자/합성 비대칭이 여기서 정확히 드러남.

## §6. 연관: note 42 의 dual 특성화

이는 note 42 의 **fold-structured = Lens-expressible** 에 대한
concrete 예.  slashCharFn 은 fold-structured 가 아니므로
Lens 없음.  rawACharFn 은 fold-structured 이므로 Lens 있음.

## 변경 이력

- 2026-04-24: leaf/slash 비대칭의 Lens 측 manifestation 기록.
  `RawACharLens.lean`, `SlashCharNotFold.lean`.
