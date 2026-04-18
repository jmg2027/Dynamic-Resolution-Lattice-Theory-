# Session Handoff — 2026-04-18

## Branch
`claude/tail-eigenvalues-explanation-0ynQx` (pushed)

## Session Goal
비판자의 "꼬리 eigenvalue" 질문 → Schubert/FM 기하학 정식화 →
α_GUT 수비학 반박 → ε₀ 도출 시도 → 기하학적 1원칙 적용.

## Honest Classification (A)/(B)/Missing

### (A) 단단한 결과 — 증거 있고 재현 가능

| # | 결과 | 실험 | 증거 |
|---|---|---|---|
| 1 | $\chi(\text{FM}_1(\Gr(3,5))) = 10$ = ch04 hinges | FND_011 | Gaussian binomial 직접 계산 |
| 2 | $\chi(\text{FM}_2(\Gr(3,5))) = 150 = 6 \times 25$ | FND_011 | Blow-up 공식 |
| 3 | Middle Betti $b_{12}(\text{FM}_2) = 24$ = SU(5) adjoint | FND_011 | 계산 결과 |
| 4 | $\int \sigma_1^{12}$ on $\Gr^2 = 25 = d^2$ | FND_011 | Plücker 교차 |
| 5 | Swap involution formal definition | FND_012 | $d_\text{indep} = 2\lceil a/2\rceil + 3\lceil b/2\rceil$ |
| 6 | det(G_h) at symmetric ∂(Δ⁵): (1, 1, 3/4, 0) | FND_016 | 기하 직접 계산 |
| 7 | Regge action at symmetric = 41.94 | FND_018 | 직접 dihedral 계산 |
| 8 | Tensor Schur-Weyl: 25 = 15 + 10 | FND_017 | GL(5) irrep 분해 |


### (B) 시도 중 — 수학 언어 붙였지만 내재 motivation 부족

| # | 시도 | 문제 |
|---|---|---|
| 1 | ε₀ = α_GUT/(2π) | 2% 일치, but no derivation (FND_015) |
| 2 | ε₀ = (1/4)^4 | 3% 일치, 지수 4 unmotivated (FND_016) |
| 3 | Clifford $\Lambda(\mathbb{C}^5) = 32$ | 자동 (2^5), DRLT가 Clifford 곱셈 요구하는지 미확인 |
| 4 | Tensor tower (C^5)^⊗n | Schur-Weyl은 generic tool, DRLT 특이성 없음 |
| 5 | "2.4% = α_GUT 구조적" | 순환 정의 제거 후 통계 유의 안 나옴 (FND_014) |
| 6 | δ_AAA = π 변분 유도 | 내 2D 파람에서 재현 안 됨 (FND_019) |

### Missing — Grand picture 책임지려면 필요

1. **Level 간 functor 명시**
   - Gr(3,5) → ∂(Δ⁵) → FM_N의 환원 map
   - Clifford → tensor tower의 antisymmetrizer
2. **Swap involution 내재성**
   - ch02 정의가 d=5 attractor를 "결과"로 주는지 "가정"으로 내장하는지
3. **EXP-047b 복원**
   - 책의 δ_AAA = π 변분 유도 원본 확인
4. **FM compactification type 명시**
   - Real FM? Complex FM? With marked points? Stable map?
5. **ε₀의 제1원리 도출**
   - 현재까지 모든 시도 numerical matching 수준


## Experiments This Session

| ID | Title | Status | Key Result |
|---|---|---|---|
| FND_011 | FM cohomology Gr(3,5) | ✓ 12/12 | $\chi(\text{FM}_N) = 5^N(N+1)!$ |
| FND_012 | Swap involution formalized | ✓ 12/12 | d=5 attractor (caveat) |
| FND_013 | 2.4% perturbative consistency | ⚠ 7/7 but overclaimed | Superseded by FND_014 |
| FND_014 | Honest critical review of FND_013 | ✓ 3/5 | Two-route match strong, empirical test weak |
| FND_015 | ε₀ = α/(2π) conjecture | ⚠ 5/5 | 2% fit, not derivation |
| FND_016 | Geometric det(G_h) from simplex | ✓ 5/5 | (1, 1, 3/4, 0) rigorous |
| FND_017 | Tensor fractal tower | ✓ 9/9 | 25 = 15+10 (Sym+Λ) |
| FND_018 | Regge action direct compute | ⚠ 1/3 | S=41.94 suggestive |
| FND_019 | Variational Regge scan | ✓ 1/1 | δ_AAA=π unreachable in 2D param |

## Key Open Questions for Next Session

1. **EXP-047b 찾기**: 책의 δ_AAA=π 유도 어디?
2. **Full 2-param Regge scan**: (θ_2, θ_3) 자유로 δ_AAA=π 찾고 S 값 확인
3. **Level functor 작성**: ch04 내 Gr(3,5) ↔ simplex 동일시 명시
4. **ch02 swap 정의 재검토**: d=5 fixed point이 내재적인지 정의 내장인지
5. **FM compactification type 결정**: Fulton-MacPherson (algebraic) vs 다른 variant

## Infrastructure
- Lean: 65 files, ~770 theorems, 0 sorry (unchanged)
- Commits this session: 9 (FND_011 through FND_019 + analyses)

## Earlier Open Problems (from 2026-04-16 HANDOFF, still pending)
1. DRLT 원론 구현 (drlt-elements/)
2. 이론적 엄밀성 갭 15개
3. θ_QCD bare value > nEDM 한계
4. T_CMB +3.7%

## Meta-Lesson from This Session
- 수학 언어를 붙이는 것과 도출하는 것은 다름
- 7-level grand picture를 예쁘게 정렬하면 자기검정 타이밍
- Functor 없는 level list는 grand picture가 아님
- Numerical matching은 증명이 아니라 suspicion
- ε₀ 도출 실패 = 진짜 open gap, 가릴 필요 없음
