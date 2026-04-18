# Foundations — Handoff

## Identity
**수학-물리 브릿지 (Derivation Chain).** 공리→ℂ→d=5→Gram→물리의 대수적 뼈대.
순수 수학도 순수 물리도 아닌 유도 사슬 자체. `CLAUDE.md` 참조.

## Status: ACTIVE (Session B 확장 진행 중)
Core (FND_001–010) STABLE, Session B 확장 (FND_011–033)은 진행 중.

## Completed (Core, FND_001–010)
- Frobenius → ℂ uniqueness (ch01, paper1)
- d=5 atomic decomposition (ch02, paper1)
- (3,2) uniqueness + SU(5) emergence (ch03, FND_010)
- δ(AAA)=π, det(SST)=2/3, c=2 (ch05, FND_003-006)
- Occupation fraction 10 values, 206 states (ch21, FND_007-010)
- Trace conservation Σ Δ_i = 0 (ch12)

## Session B 확장 (FND_011–033)

### Verified
- n=5 unique alive decomposition, ∀v≥6 ambiguity
- Binet–Cauchy 1+12+12=25 channel decomposition (ch08)
- Claim 2': scale-invariance ⟺ confluence (FND_032)
- FM cohomology 패턴 χ=5^N·(N+1)! (N=1..5)
- Gr(3,5) Schubert cell count = 10

### Refuted (honest negatives)
- FND_013: 2.4% = α_GUT 범용성 (체리픽)
- FND_019: 1-param Regge scan (잘못된 family)
- FND_021: w² = 9/(25π²) (0.4% gap)
- FND_025–026: Gravity Λ^k / shape-only 형식

### Open Gaps (세부: `notes/GAPS_REGISTER.md`)
- G-D2: Binet–Cauchy에서 중력 위치
- G-D3: 중력 조합공식
- G-D6: ε₀ 함수형태 f(N_H, d) — FND_015가 ε₀ = α/(2π) 추측
- G-M_i: 기하적 가중치
- G-N1: Regge S_var = 56.79의 의미

### Lean 형식화 (수학 트랙 소속)
5 파일 in `critical-line/lean/PmfRh/`:
ScaleInvariantFoundation, DimensionBridge, BinetCauchy, ScaleConfluence, GrassmannianData.
foundations/ 쪽에서는 FND 파이썬 실험만 관리.

### 핵심 realization
"4D machine-verified" = OVERCLAIM.
"n=5 uniqueness machine-verified, atoms {2,3} premise" = ACCURATE.

## Potential Future Work
1. **f_occ 미확인 값 (3/4, 4/5)**: 물리적 대응 찾기
2. **Higher-d simplex**: d=7,11 등에서 DRLT 구조 탐구
3. **Categorical formulation**: 심플렉스 기하를 범주론으로 재구성
4. **ε₀ 함수형태 (G-D6)**: FND_015 추측 확장
5. **중력 위치/공식 (G-D2, G-D3)**: Binet–Cauchy 재검

## Experiments: 33 (FND_001-033)
## Papers: paper1, paper2
## Book: Part I (ch01-03), Part II (ch04-05, ch08), ch21
## 상세: `notes/FORMAL_FOUNDATION.md` (DAG), `notes/GAPS_REGISTER.md` (열린 문제)
