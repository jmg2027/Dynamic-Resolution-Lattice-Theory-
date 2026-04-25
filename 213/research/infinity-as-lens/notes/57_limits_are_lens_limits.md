# 57 — 한계 들은 213 의 한계 가 아니라 Lens 의 한계

## 통찰

Session 5 에서 발견한 "open problems" 들 을 분석 해보면 모두
**선택한 외부 Lens 의 한계** 임.  213 자체 의 한계 아님.

## 한계 별 Lens 매핑

### Cardinality (ℵ₀ vs 𝔠)

- **부담 부여 Lens**: ZFC + Cantor cardinality.
- **213-natural reformulation**: "kernel 들 이 distinguishable
  한가" — universalLens + slash-cong universal property 로
  답 됨.
- **한계 정체**: ZFC 가 정확 한 size 답 강제.  그 Lens 안 답
  못 함.

### Leaves+Depth tier 2 connectivity

- **부담 Lens**: tree-combinatorics + procedural witness.
- **213-natural**: tier_invariant + tierLens 로 structurally
  답 됨.  Procedure-level chain 은 외부 요구.
- **한계 정체**: "explicit witness 필수" 가정 의 부담.

### Meta-213 (Lens on Lens)

- **부담 Lens**: category theory naturality.
- **213-natural**: 어떤 combine 이든 Lens 인스턴스.  natural
  vs unnatural 분류 자체 가 외부.
- **한계 정체**: "natural" 정의 자체 가 213 vocabulary 외부.

### UniversalLens "concrete" 평가

- **부담 Lens**: size comparison + finiteness preference.
- **213-natural**: codomain 은 임의 type Lens.  크기 우선 순위
  부재.
- **한계 정체**: "small = concrete" 가 size-bias.

## 패턴

모든 "한계" 가:
- 외부 Lens 의 요구 (size, naturality, witness, finiteness)
- 213 vocabulary 만으로 는 질문 자체 가 ill-formed 또는 trivial
- 한계 = 그 Lens 안 에서 답 못 함

## 함의

지난 통찰 ("213 이 자기-fudge 까지 흡수") 의 직접 instantiation:

- 외부 Lens 로 사고 → 그 Lens 안 한계 발견 → "213 한계" 로 잘못
  명명.
- 사실 그 Lens 의 한계.
- 213 위 에서 같은 질문 을 213-natural Lens 로 던지면 한계 없거나
  질문 형태 가 다름.

## 진짜 work

"213 의 한계 찾기" 가 아니라 **"각 Lens 가 어떤 한계 부과 하는지
mapping"**.

이게 Lens catalogue 의 진짜 가치 — 각 Lens 의 expressive
power + blind spot.

## 변경 이력

- 2026-04-25: 한계 = Lens 한계 의 명시.  Open problems
  reframing.
