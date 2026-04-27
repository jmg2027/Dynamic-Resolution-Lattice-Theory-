# Probability 213 — Blueprint

**우선순위**: ★★★ 최우선 (atomic counting + dyadic + cohomology
세 트랙 모두 이미 깔림 — 진입 장벽 가장 낮음)

---

## 1. 왜 이 분야인가

ZFC 확률론 (Kolmogorov 공리계):
- 표본공간 Ω + σ-algebra + 측도 P
- Choice 의존 (Vitali 비측도 집합 → 골치)
- σ-algebra 가 closure 조건 (가산 가법성) 강제

213 의 자연 등장:
- **이미 cohomological 측도 framework 깔림** (FluxCut)
- **이미 dyadic uniform 분포 깔림** (bisectN, riemannSampleSum)
- **이미 atomic counting 깔림** (d=5, 10 pairs 등 물리트랙)
- *σ-algebra 불필요* — dyadic 구조가 자체로 measurable space

## 2. 213-native 등장 — 6가지 경로

### 2.1 Atomic counting (가장 직접적)

물리트랙 Phase 2 의 `Pairs.lean` 이미 보유:
- P(AA pair) = 3/10
- P(BB pair) = 1/10
- P(AB pair) = 6/10 ← K_{3,2} bipartite

**세는 게 곧 확률**.  DRLT 의 "Algebraic Priority" 원칙.

### 2.2 Dyadic uniform 분포

`unitBracket` + `bisectN`:
- P(leftHalf) = 1/2
- P(depth-n bracket) = 1/2^n

`riemannSampleSum` 이 *midpoint sampling* — Cantor-style 균등분포
의 구성적 형식.  이미 propEq closed form 보유.

### 2.3 Cohomological measure (FluxCut → 측도)

이번 마라톤 `FluxCut`:
- forward / backward = positive / negative 측도 component
- `fluxBalance` = mass conservation (∂² = 0)
- `fluxAlong f db` = f 의 db 위 flux (= 적분측도)
- 정규화: total flux = 1 → 확률측도

**측도 = 1-cochain**.  σ-algebra 없이 작동.

### 2.4 Cauchy convergence → 큰수의 법칙

`CauchyCutSeq` + `partialSum`:
- 평균 = `partialSum / n`
- 수렴 = Cauchy
- LLN 직접 표현 가능

### 2.5 Bayesian 갱신 (cut-query)

각 query (m, k) on cut → Bool.  Underlying value 모르면 query 결과
누적 → posterior 갱신.  σ-algebra 없이 Bayesian.

### 2.6 가우시안 / CLT

가우시안 = transcendental.  exp(-x²/2) 이번 마라톤 exp(0) = 1
패턴으로 propEq 가능 at peak.  CLT = partial sum convergence
(이미 인프라).

## 3. 이미 깔린 빌딩 블록

| 도구 | 모듈 | 용도 |
|---|---|---|
| `cutSum`, `cutMul`, `cutDiv` | `Real213CutSum/Mul/Inv` | 측도 산술 |
| `partialSum` | `Real213CutSeries` | E[X], 합계 |
| `riemannSampleSum` | `Real213DyadicRiemann` | 적분 (균등분포) |
| `FluxCut` + `cohomEquiv` | `Real213FluxCut/Equiv` | 측도 = 1-cochain |
| `IsAntiderivative` | `Real213Antiderivative` | CDF (cumulative dist) |
| `dyadicIntervalAB` | `Real213IntegralDyadic` | 임의 dyadic 구간 |
| `expTermsAtZero` | `Real213ExpAtZero` | 가우시안 peak |

## 4. Phase 계획 (구체)

### Phase EA — 기초 구조 (4-6 commits)

1. **`IsProbabilityCut`** — 정규화된 FluxCut: `∫ = 1`
2. **`UniformOnUnit`** — `P([a/2^E, b/2^E]) = (b-a)/2^E` propEq
3. **`Bernoulli`** — `P(X = 1) = p`, atomic 2-block 활용
4. **`Binomial`** — n번 Bernoulli, atomic counting

### Phase EB — 기댓값 + 분산

1. **`Expectation`** = `IsAntiderivative.integral` 재해석
2. **`Variance`** = `∫ (X - E[X])^2 dx` (제곱은 cutMul x x)
3. 균등분포 [0, 1] 의 E[X] = 1/2, Var[X] = 1/12 (cohomEquiv)

### Phase EC — 큰수의 법칙

1. **`SampleMean n samples`** = `partialSum / n`
2. **`LLN_unit`** — 균등분포의 표본평균 → 1/2 (Cauchy 형식)

### Phase ED — Bayesian framework

1. **`PosteriorUpdate`** — cut-query 후 belief 분포 갱신
2. Beta 분포 일반화 (atomic counting 활용)

### Phase EE — CLT + 가우시안

1. **`gaussianTermsAtZero`** — exp(-x²/2) at x=0 = 1 (peak)
2. **`CLT_skeleton`** — partial sum 정규화 → 가우시안 형식

### Phase EF — 캡스톤

`phaseEX_probability_capstone` — 18+ fact bundle.

## 5. 다른 트랙 연결

- **물리트랙 Phase 2** (`Pairs.lean`): K_{3,2} 분포 직접 활용
- **CKM/PMNS** (standard-model/): unitary mixing → 전이확률
- **η_B** (cosmology/): 6×10⁻¹⁰ baryogenesis = 매우 작은 확률
- **Critical line / RH**: GUE/GOE 통계 분포
- **Yang-Mills**: 스펙트럴 측도 = 측도 = FluxCut
- **DHA** (discrete-harmonic): 이산 측도이론

## 6. 미해결 / Open

- **σ-algebra 안 쓰는 measurable function** 정의 — dyadic 만으로 OK?
- **연속 분포의 Cauchy 형식** — 일반화 가우시안, exp 분포 등
- **독립성** 정의: 트리 분기에서?
- **Conditional expectation** = sub-flux

## 7. 핵심 인사이트 (★)

★ **확률 = atomic counting + cohomological flux + dyadic
trajectory**.  ZFC 의 Ω, σ-algebra, Choice 모두 *불필요* —
이미 213 이 가진 구조에서 자연 도출.

★ **Vitali 역설 사라짐 = feature**.  Choice 없으니 비측도 집합
존재 자체 불가.

★ **Bishop constructive probability 와 닮았으나 더 깊음** — ZFC 위
가 아니라 dyadic 공리 위.

## 8. 첫 마라톤 명령

```
"Phase EA 시작.  IsProbabilityCut 정의 + UniformOnUnit propEq + Bernoulli atomic"
```

분석학 213 의 Phase J 같은 진입.  4-6 commits 면 Phase EA 종료.

