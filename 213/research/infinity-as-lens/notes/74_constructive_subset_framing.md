# 74 — Constructive subset: ZFC 의 임의성 vs 213 의 explicit witness

Paper 1 의 Risk 1 (Power set reduction §5.2) + Risk 2
(transcendental cuts §7) 의 통합 framing.  두 risk 가 같은
구조 — "ZFC 가 임의성 commitment, 213 은 explicit witness 만".

## 두 risk 의 공통 구조

| Concept | ZFC | 213 |
|---------|-----|-----|
| Subset of X | 임의 (P(X) axiom) | slash-congruence 만 = Lens kernel |
| Real number | 임의 Dedekind cut | constructive Cauchy (explicit witness) |
| Choice | global axiom | Lens specification (universalLens) |
| Infinity | Inf axiom | Raw 의 unbounded depth (induction 자동) |

각 행 모두 동일 패턴: ZFC 가 axiomatic commitment, 213 이
constructive subset.

## "약점 이 아니라 design choice" 의 정확 한 의미

ZFC 의 임의성 axioms 는 **LEM 자동 commitment** 동반:
- P(X) axiom 은 임의 binary relation 을 set 으로 인정 (decidable
  여부 무관).
- Dedekind cut 의 "임의 분할" 은 LEM 으로 dispatch 되는 case
  split 가능.
- Choice 는 직접 LEM 함의.

213 은 이 commitment 를 **거부** — falsifiability contract
(AXIOM.md §5.2.1) 의 직접 귀결:
- 모든 결과 가 Lean 4 core + Raw 공리 만으로 derive 가능 해야 함.
- Classical.choice / LEM / native_decide 등 외부 axiom 추가 일절
  금지.

→ 213 framework 안 표현 가능 한 것 만 다룸.  LEM 자동 dispatch
가능 한 임의성 부재.

## 구체 결과

### (a) Power set: Lens kernel space ⊊ "임의 subset"

`NoDepthParity.lean`: depth parity 가 Lens kernel 이 아님.  즉
임의 binary relation 이 fold-structured 아닐 수 있음.  Raw 위
모든 부분 분류 ≠ 213 framework 안 표현 가능 한 부분 분류.

213 의 답: 모든 slash-congruence 가 Lens kernel (universalLens).
**Lens 로 표현 가능 한 부분 분류 만** framework 안.  더 많이
주장 안 함.

### (b) Real number: constructive Cauchy ⊊ Dedekind 임의 cut

`MonotonicBoundedCauchy.lean` (note 73): 일반 `∀ (m, k) cut`
closure 는 LEM 필요.  213 은 **각 (m, k) 의 explicit witness**
만 제공.

- Pell (Sqrt2Cut): algebraic invariant 로 양쪽 explicit.
- Euler / Wallis: specific cuts (m/k ≥ 3, ≤ 2 등) explicit.
- Monotonicity instance + propagation helper 로 추가 cut 도
  explicit witness 통해 derive 가능.

**임의** (m, k) 자동 closure 가 부재 — feature.

### (c) Choice: universalLens 로 환원 (이미 closed)

`UniversalQuotLens.lean` + `ChoiceResolved.lean`: 임의
slash-congruence E 에 대해 explicit Lens with kernel = E.
LEM / Choice 없이 each instance 의 explicit witness.

## Paper 1 의 핵심 메시지 정정

§5.2 (Power set), §7 (Cauchy demos), §8 (open work) 모두
같은 줄 — **"213 은 constructive framework, ZFC 의 임의성
commitment 거부"**.

따라서 Risk 1 / Risk 2 / Risk 3 가 다른 risks 가 아님.  하나
의 **falsifiability contract 의 일관 된 귀결**.

§1 (introduction) 에서 이 framing 을 핵심 메시지 의 일부 로
명시 — "213 = constructive subset of ZFC's commitments,
falsifiable by axiom-addition test".

## §8.4 의 open work 정리

이전 의 "임의 (m, k) cut closure" 등 은 더 이상 open 이 아님
— LEM 없이 closure 가 불가능 함이 확인 됨.  이는 **closed
result**: 213 framework 의 정확한 boundary 가 식별 됨.

진짜 open work:
- 각 demonstration 의 cut 을 더 sharpen (e.g., Euler 의 m/k ≤
  5/2 까지 below cut 확장).
- Power set 의 strict subset 관계 의 constructive lemma
  (Lens kernel ≠ 임의 binary relation 의 형식화).
- 새 Lens family 추가 (catalogue 확장).

## 변경 이력

- 2026-04-25: 73 + 74 작성.  Paper 1 의 세 risk 가 통합 된
  design choice 로 reframed.  LEM commitment 거부 가
  falsifiability contract 의 직접 귀결 임 명시.
