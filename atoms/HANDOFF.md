# Atoms Handoff — 2026-04-15

## 핵심 결과: f_occ(ε²) = α_GUT on N=4 Flat Manifold (0.10%)

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

### 2. 0.1% 잔차
ε²-α_GUT(1+α_GUT) = 1.2×10⁻⁵. 초월적 방정식이므로 exact 대수적 항등식 불가능.
Higher-order geometric correction 또는 manifold refinement 필요.

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
Next: ATM_031
```
