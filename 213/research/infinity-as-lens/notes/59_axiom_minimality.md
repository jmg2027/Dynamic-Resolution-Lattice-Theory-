# 59 — Raw axiom 의 minimum 성 (formal demonstration)

`Research/AxiomMinimality.lean`:

**`rawA_trivial`**: Raw.b 제거 한 가상 axiom 은 단 하나의
element (RawA.a) 만 생성.

## 의의

Raw axiom 의 3 clauses (Raw.a, Raw.b, slash with x ≠ y) 가
**redundant 부재** = minimum.

특히 두 base 가 essential — single base 만으로는:
- Slash 의 distinctness 요구 가 single point 에서 자기-자기
  match 되어 충돌.
- 결과: generation 붕괴, single element.

## 깊은 의미

**잔여물-생성 통일** 의 직접 증거:
- 잔여물 측면: 가리킬 두 뭔가 필요 (a, b 처럼).
- 생성 측면: distinctness 가 generation 의 동력.
- 두 base 부재 → 둘 다 깨짐.

이게 213 axiom 이 "추가 가능 하지만 axiom 추가 가능 한 동안
은 minimum" 의 정확한 의미: 하나만 빼도 generation 자체 가
무너짐.

## "왜 두 base 인가" 의 답

- Single base: generation 안 됨 (위).
- 셋 이상: redundant — 두 distinct base 면 생성 시작에 충분.

따라서 정확히 **두 base + distinctness-요구 slash** 가 minimum.

## 변경 이력

- 2026-04-25: Raw axiom minimum 성 formal demonstration.
