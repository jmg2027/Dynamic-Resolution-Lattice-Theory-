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

## Recent (FND_034, 2026-04-18)

**Phase A1 roadmap (G4 "ε₀ closed form") - FND_034 outcome:**
- High-precision variational: w* = 0.19026442 (Brent, tol 1e-14)
- ε₀_eff = (1 − w*²/(3/2·α_GUT))/2 = **0.003778**
- α_GUT/(2π) conjecture = 0.003870 → **deviation -2.57%**
- **FND_015의 "2% 일치" 우연이었음. 정확한 identity REFUTED.**
- 살아남은 구조: Identity B `w*² = (3/2)α_GUT·(1 − α_GUT/π)`
  residual +7.26e-6 (order (α_GUT/π)² = 6e-5). 1/(2π) leading coefficient
  97% 유효. 잔차 2.6% 구조 correction c1=0.974 설명 대기.
- **결론**: G4는 blocking이 아님. 진짜 decisive는 **G-M_i 기하 가중치**.
- **다음 실험**: FND_035 (Binet-Cauchy canonical weights M_i).

## Recent (FND_035, 2026-04-18)

**Phase A2 roadmap (G-M_i 기하 가중치) - FND_035 outcome:**
- M_i = Σ√det(G_h) per class 직접접근 **REFUTED**.
- 기하 Σvol: {AAA=0.95, AAB=5.89, ABB=2.12} vs Book {13.75, 1.0, 3.5}
  → 순서 **완전 반대**, 기하 단순 접근 불가.
- Empirical back-fit: M_weak=3.51✓, M_EM=0.98✓, M_strong=15.46 (book 13.75)
  → **Book의 M_i는 관측 Δ_i에서 역산된 fit value**.
- 심각한 의미: 책의 "0 free parameter" 주장에 **숨은 3 자리** (M_S, M_W, M_EM).
- **핵물리 3-7% 오차의 진짜 원인 추정**: M_i가 derive 안된 fit이면,
  a_V, a_S, a_C도 비슷한 fit 성격 있을 수 있음.
- **Routes 남은 것**: Regge deficit-based weight, Binet-Cauchy exponent
  조합 (c^k·C(n_A,3−k)·C(n_B,k)), S(N) Langlands 조합.

## Experiments: 35 (FND_001-035)
## Papers: paper1, paper2
## Book: Part I (ch01-03), Part II (ch04-05, ch08), ch21
## 상세: `notes/FORMAL_FOUNDATION.md` (DAG), `notes/GAPS_REGISTER.md` (열린 문제)
