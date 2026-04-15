# Atoms Handoff — 2026-04-15

## 핵심 결과: Born-Screening Duality at d=5 ★★★

### 최신 세션 (ATM_035-038 + ch10 업데이트)
- **ATM_035**: IE 개선 median 3.5%→**3.1%**, <5% 76→**81**. DEEP_PAIR + f14-pair.
- **ATM_036-037**: Born gap ≈ σ_cross 발견. sin(2φ)=8/9 → μ=7/9 → 7/8 EXACT.
- **ATM_038**: ★★★ **Born-Screening 정리**: 3개 screening 상수 독립 유도, d=5 유일성.
  - σ_cross = 2μ/(1+μ) = 7/8 EXACT
  - σ_sp_odd = (1+μ)/2 + 1/(N_S²dN_T) = 9/10 EXACT
  - σ_sp_even = (1+μ)/2 - μ/(dN_T²) = 17/20 EXACT
  - Uniqueness: 2d²-13d+15=0 → d=5 only integer
- **ch10**: 418→705줄, 6→19 정리. Born-Screening + IE table 추가.

### 이전 세션 (ATM_032-034)
- **ATM_032**: N=2 정류 방정식, ε²(N=2)≈(3/2)α_em (-0.98%). 5/5.
- **ATM_033**: σ_same_s = 1/N_T + c²α_GUT 기하학적 유도. 5/5.
- **ATM_034**: ζ₉ 물리: SSS=0 on N=4, 9 채널, 0.001%. 4/4.

### 이전 세션 성과
- atoms/theory/complete_theory.md: 통합 이론 문서 (330줄, 18섹션)
- atoms/theory/integer_catalog.md: 모든 정수 출처 (수비학 0)
- atoms/theory/epsilon0_derivation.md: ε₀ = (l_Pl/R_H)^{6/151} 엄밀 유도
- papers/paper6_simplex_coupling.tex: 논문 작성 완료 (433줄)
- Ry = α²m_e/N_T: Rydberg의 1/2 = 1/N_T (시간 차원 수)

### 도출 체인
```
QM 독립성 → orthogonal B vectors → dihedral = π/2
→ N_flat = 4 → δ(AAA) = 0 (strong sector decouples)
→ ∂S_boundary/∂ε = 0 (초월적 방정식)
→ ε² = 0.02490 (bare coupling)
→ f_occ(ε²) = ε²/(1+ε²) = 0.02429 = α_GUT ± 0.10%
```

### N-simplex manifold 구조
| N | δ(AAA)/π | ε_max | ε² | f_occ | f_occ/α_GUT |
|---|----------|-------|-----|-------|-------------|
| 2 | 1.0 | 0.1041 | 0.01084 | 0.01072 | 0.441 |
| 3 | 0.5 | 0.1344 | 0.01807 | 0.01775 | 0.730 |
| **4** | **0.0** | **0.1578** | **0.02490** | **0.02429** | **0.999** |
| 5 | -0.5 | 0.1765 | 0.03116 | 0.03022 | 1.243 |

### Exact Analytical Formulas
```
cos(θ_AABt) = ε / √(1-2ε²)          [대수적, exact]
cos(θ_ABet) = -ε² / (1-2ε²)         [대수적, exact]
det(AABe) = 1 - 2ε²                  [대수적, exact]
det(ABet) = 1 - ε²                   [대수적, exact]
S(ε,N) = S_shared(N) + 3N[f₁(ε)+f₂(ε)]  [초월적, closed-form]
S(0,N) = (7N+8)π                     [산술적, exact]
```

### 대칭 manifold (B₃ = -B₂)
- δ(AAA) = π (exact), δ(AABe) = π (exact) — 물질 섹터 rigid
- δ(AABt), δ(ABet)만 ε-의존 — 게이지 섹터만 동적
- 22 = d² - N_S = 25 - 3 (hinge count = channel count - frozen spatial DOF)

---

## 실패한 접근 (반복 금지)

### ✗ Channel-weighted Regge action
c^k 또는 c^{2k} 가중치로 hinge 면적 수정 → α_GUT 매치 악화.
**Standard (unweighted) Regge action이 최선.** 채널은 action과 별도로 세야 함.

### ✗ Lagrange multiplier R(G) = r₀
R_SSS에 topological floor (1/22) 존재. 아무 ε에서나 target hit 가능 (단조함수).
Constraint approach는 self-consistent하지 않음.

### ✗ Full variational (ε, η, φ₂) optimization
Global max: (ε=0.099, η=0, φ₂=0.484π). α와 무관한 값.

### ✗ A 벡터 temporal leakage
η ≈ 0.476에서 R=α_GUT 달성하지만, action extremum 아님. 파라미터 튜닝.

---

## 미해결 문제 (우선순위)

### 1. N=2 → 수소 물리
eps²(N=2) = 0.01084 ≈ (3/2)α_em (1%). N=2 manifold 기하 → IE(H) = Ry 메커니즘.

### 2. 0.1% → 0.001%: 유한 ζ 절단 (ζ₉ self-consistency)
기본 방정식: cos(F(x)) = -x/(1-2x), F는 순수 대수적, cos만 초월적.
S = 2πB(ε) - T(ε) 분해에서 B'/β = 1 exactly.

전파자 ζ(2)를 유한 합으로 절단하면:
- N→∞ (exact π²/6): gap = 0.104%
- **N=9: gap = 0.001%** ← self-consistent!
- 9 = C(5,3)-1 = 10-1 = 비-SSS Binet-Cauchy 채널 수 (SST:6+STT:3)
- N=4 flat에서 SSS decouple → 9 mixed 채널만 전파자에 기여
- ζ₉(2) = Σ₁⁹ 1/n², α₉ = 1/(25ζ₉), period₉ = √(24ζ₉)
- 이 period로 Regge max → f_occ = α₉ to 0.001%

핵심 질문: ζ₉ vs ζ(∞) 중 어느 것이 "맞는" 전파자인가?

### 3. Screening from manifold
8개 screening 상수의 manifold 기하학적 도출. 현재는 현상론적.

---

## Screening Constants (기존, 유지)
```
σ_cross = 1-n_S/(d²-1) = 7/8
σ_same_s = 1/n_T + c²α_GUT = 0.597
σ_ns→np(even) = 1-n_S/(d(d-1)) = 17/20
σ_ns→np(odd)  = 1-n_T/(d(d-1)) = 9/10
σ_same_p(p=2) = n_S/(n_S+1) = 3/4
σ_same_p(p≥3) = n_T/(n_T+1) = 2/3
σ_df→p = 1-α_GUT = 0.976
Δ_pair = n_S/π² = 3/π²
```

## Experiment Map
```
ATM_014-022: Screening model (median 3.5%, 유지)
ATM_023: 폐기 (틀린 기하)
ATM_024: Δ⁴ single (5/5)
ATM_025: 2-simplex manifold (3/4, phi3 수정 필요)
ATM_026: Dihedral vs epsilon (6/6, 대칭 manifold 발견)
ATM_027: Free A vectors (4/5, 실패 기록)
ATM_028: Full variational (4/4, 실패 기록)
ATM_029: N-simplex manifold (6/6) ★ BREAKTHROUGH
ATM_030: Analytic action (4/4, exact formulas)
ATM_031: Finite zeta cosine (4/4, ζ₉ self-consistency)
ATM_032: N=2 hydrogen mechanism (5/5) ★ N=2 stationarity
ATM_033: Screening from manifold (5/5) ★ σ_same_s geometric
ATM_034: Zeta-9 physical meaning (4/4) ★ SSS decoupling
ATM_035: Complete-shell pair (4/4) ★ median 3.5→3.1%, <5% 76→81
ATM_036: Born screening exploratory (4/4) gap≈σ_cross
ATM_037: Born phase constraint (5/5) sin(2φ)=8/9→7/8
ATM_038: Born screening exact (7/7) ★★★ 3 constants, d=5 unique
Next: ATM_039
```
