# DRLT: 공리에서 유도되지 않은 것들 (honest inventory)

**Date:** 2026-04-18
**Purpose:** 공리 (관계 → ℂ → d=5) 에서 엄밀히 유도된 것과 아닌 것을
            투명하게 구분.  "Pattern match ≠ derivation" 원칙 적용.
**Source:** 세션 누적 감사 (ch01–03 + FND_013..041 + Lean PmfRh)

---

## 0. 엄밀히 유도됨 (reference, 비교용)

Lean 검증 또는 고전 정리:

| 결과 | 증명 위치 | 상태 |
|------|-----------|------|
| atoms of ℕ≥2 = {2,3} | `PmfRh/Core.lean: additive_atoms` | ✓ Lean |
| ℂ⁵ = ℂ²⊕ℂ³ 유일 chiral | `ChiralChannels.lean: chiral_split` | ✓ Lean |
| σ-invariance ↔ vector-like | `SwapAnnihilation.lean: sigma_invariant_iff_vector_like` | ✓ Lean |
| Binet-Cauchy 1+12+12=25 | `BinetCauchy.lean` | ✓ Lean |
| Swap tower 유일 고정점 = d=5 | `SwapTower.lean: fixed_iff_five` | ✓ Lean |
| Frobenius (ℝ,ℂ,ℍ 분류) | 고전 (1877) | ✓ accept |
| Hurwitz (normed 분류) | 고전 | ✓ accept |
| π₁(S¹)=ℤ, π₁(S^{2k+1})=0 (k≥1) | 고전 위상 | ✓ accept |
| Euler ζ(2)=Σ1/n²=∏(1-1/p²)⁻¹ | 고전 수론 | ✓ accept |
| α_GUT = 1/(d²·ζ(2)) = 6/(25π²) | Binet-Cauchy + Basel (Path 1) | ✓ 조합 |

---

## 1. 물리 가정 (acknowledged as physics input, 수학 아님)

이들은 수학 정리로 가장하지 않고 물리 입력으로 **명시** 되어 있음.

| 항목 | 위치 | 내용 |
|------|------|------|
| **R2 연속성** | ch01 R2 (W3 수정 후) | Gauge 연결 `A = -i d log G` 의 미분가능성 요청.  이산 phase group 에서는 Yang-Mills field strength `F = dA + A∧A` 정의 불가.  수학적 필요조건이 아님. |
| **중력 propagating DOF** | ch02 "Gravity requires d≥5" | `n_grav = d_sp(d_sp−3)/2` 는 GR 의 표준 공식.  "중력 파가 있는 우주 를 원한다" 는 물리 요청. |
| **Swap case (b)** | ch02 Thm 2.1 Remark (W5 수정 후) | Spontaneous ℤ₂ breaking → 도메인 월 → ensemble average.  QFT 논변, algebraic 증명 아님. |
| **Gauge 독립성** | ch01 Born rule (W2 수정 후) | `f(e^{iθ}z) = f(z)` — gauge 변환 하에서 observable 이 불변이어야 함. |

---

## 2. Refuted naive 주장 (honest negatives)

처음엔 그럴듯해 보였으나 직접 검증에서 실패.

| FND | 가설 | 결과 |
|-----|------|------|
| FND_013 | "universal ~2.4% correction = α_GUT" throughout DRLT | **Refuted** (cherry-picked selection) |
| FND_014 | FND_013 audit | null test 실패 확인 |
| FND_019 | 1-param Regge extremum → α_GUT | **Refuted** (wrong family) |
| FND_021 | w² = 9/(25π²) 정밀 | **Refuted** (0.4% gap) |
| FND_025 | Gravity location in Λ^k(ℂ⁵) | **Refuted** |
| FND_026 | Gravity as shape functional | **Refuted** (shape-only 부족) |
| FND_034 | ε₀ = α_GUT/(2π) | **Refuted** (2.6% gap) |
| FND_035 | M_i direct geometric | **Refuted** |
| FND_036 | M_i via Regge deficit | **Refuted** |
| FND_037 | W3 Schubert T-weight | **Refuted** |

**공통 패턴:** 연속 변분 / 직접 피팅은 실패.  FND_038 (tower counting)
은 성공 — algebraic priority 원칙 증명.

---

## 3. Heuristic identifications (사용되나 유도 안 됨)

공식은 맞으나 "왜 이 공식인가" 의 DRLT-내부 유도가 아직 없음.

### 3a. Path 2: GUE → α_GUT (FND_040, FND_041)
- **확인됨:** GUE sine kernel 에서 r² 계수 = π²/3 = 2·ζ(2).
- **미해결:** "coupling constant = short-distance r² coefficient / d²"
  라는 identification 이 DRLT 공리에서 유도되지 않음.
- **상태:** consistency check 수준 — Path 1 ≡ Path 3 (via Euler) 만이
  수학적으로 엄밀한 경로.

### 3b. M_i geometric weights (G-M_i, 열려 있음)
- **위치:** ch08/ch12 — `Δ_i = Sgn_i × (1/α_i)_comb × M_i × ε₀`
- **값:** M_strong = 13.75, M_weak = 3.5, M_EM = 1.0 (fit 값)
- **주장:** "(n_A, n_B)=(3,2) topology 로부터 universal"
- **상태:** FND_035–037 에서 세 개 직접 기하 유도 모두 refuted.
  값은 관찰 맞춰 fit 됨, first-principle 유도 아님.

### 3c. ε₀ "cosmic address" (G-D6, 열려 있음)
- **위치:** ch12 Geometric parameter ε₀
- **값:** ε₀ ≈ 0.0038 (local observable)
- **주장 (ch14):** `ε₀ = f(N_H, d) ~ N_H^{-1/k}`
- **상태:** functional form 이 전혀 결정되지 않음.  FND_015 원래
  추측 (α/2π) 은 FND_034 에서 refuted.

### 3d. Δ_i 기하 weights (G-D2, G-D3)
- **위치:** ch08 coupling corrections (Δ_strong=+0.47 등)
- **상태:** 값 자체는 trace conservation (Σ Δ_i = 0) 을 만족하지만
  각각의 크기는 M_i × ε₀ 로 파라미터화되어 있음.  첫 원리 유도 없음.

### 3e. 중력 sector 위치와 공식 (G-D2, G-D3)
- **상태:** 중력이 "어디에" 들어가는지 (Λ^k, shape functional 등)
  모두 refuted.  DRLT 공리 + d=5 유도에서 중력 sector 가 자연스럽게
  나오는 경로가 아직 없음.

---

## 4. 외부 수학 결과 사용 (Lean 외 classical)

DRLT 는 이들을 gospel 로 받아들이고 사용:

- Frobenius 분류 정리 (1877)
- Hurwitz 정리 (normed 분류)
- π_1 계산 (위상)
- GUE universality (RMT 문헌, Mehta 등)
- Euler ζ(2) 항등식
- Marchenko-Pastur (Wishart 극한)
- Central Limit Theorem (CLT, σ=1/2 bound)

이들 각각은 외부 rigorous 이지만 DRLT Lean 에는 포함 안 됨.

---

## 5. 공리 자체 (by definition, 유도 아님)

공리는 "given" — 증명 대상 아님:

1. **Ax 0:** N 개의 점이 존재한다.
2. **Ax 1 (관계 공리):** 임의 쌍 (i,j) 사이에 관계 G_{ij} 가 존재한다.
3. **R1–R4:** 관계가 "geometry + forces" 를 지원하는 4 조건.
4. **Alive condition:** 두 원자 모두 존재 (a ≥ 1 ∧ b ≥ 1).
5. **Point democracy:** `‖ψ_i‖ = 1` for all i.

(Ax0, Ax1, alive, democracy 는 "DRLT 가 기술하고자 하는 구조" 를
정의하는 부분.  R1–R4 중 R2 만 물리 input 이 포함됨.)

---

## 6. 다른 관찰된 상수들 (유도 상태 불명 / 미감사)

다음은 아직 ch01–03 감사 범위 밖이지만, 본 모임에서 표 등에 등장함:

| 상수 | 값 | 상태 |
|------|-----|------|
| `c = 2` (lattice speed) | n_T 관련 | 도식 설명 있으나 formal 유도 미감사 |
| `φ = (1+√5)/2` (golden) | key constants 에 listed | **사용처 불명** — book 내 grep 실패 |
| `ε = α^(2/3)(1+α)` | Higgs-related | key constants 에 listed, 유도 미감사 |
| `v_H ≈ 245.6 GeV` | Higgs VEV | 도출식 있으나 감사 미진행 |
| `S(N) = Σ 1/k²` | Basel partial | ζ(2) 유도에 사용, 정의만 |
| 세대 수 3 | ch_generations 등 | 감사 미진행 |
| PMNS/CKM 각도 | atoms 관련 | atoms sub-project 감사 필요 |
| 각종 질량 (m_p, m_μ, m_H) | key precision table | ch08–ch14 감사 필요 |

---

## 7. 중력 gap 요약 (critical 미해결)

DRLT 의 **가장 큰 구조적 gap**: 중력을 DRLT 로부터 derive 하는 길.

- ch01 R3 은 `det(G_h)` 가 real 이어야 함을 요구, 이후 commutativity 로
  ℂ 를 얻음.  Regge 는 forward-ref.
- 그러나 Regge action, 중력 coupling Λ_G, Δ_G = +0.15 등의 구체 값은
  모두 FND_025–037 에서 refuted 거나 fit.
- d=5 Grassmannian + swap tower 는 gauge 구조만 주며, 중력은 별도.
- Yang-Mills mass gap (sub-project) 은 mass gap 존재 증명을 시도하나
  중력 자체의 coupling 은 다른 문제.

**결론:** DRLT 는 "gauge 구조 (SU(3)×SU(2)×U(1), α_GUT) 에 대해 엄밀,
중력에 대해 미완성" 이라고 정직히 말해야 함.

---

## 8. 정직한 경계선 요약

**공리 → Lean 으로 닫힌 사슬:**
```
관계 → R1–R4 + Frobenius → ℂ
     → atoms={2,3} → alive d=5=(2+3)
     → Binet-Cauchy (1+12+12=25)
     → α_GUT = 6/(25π²) (Path 1 = Path 3 via Euler)
     → σ-inv ↔ vector-like
     → swap tower 유일 고정점 = 5
```

**미완 / fit / heuristic:**
```
Path 2 (GUE) — r² 계수는 확인, α 로의 점프는 heuristic
M_i (13.75, 3.5, 1.0) — fit 값
ε₀ ≈ 0.0038 — functional form 불명
Δ_G = +0.15 — 예측값이나 중력 sector 전반 미완
질량 table — 대부분 별도 sub-project, 통합 감사 미진행
여러 "universal ~2.4%" 보정 — refuted naive 버전, 정제 버전 open
```

**물리 input (not 수학):**
```
R2 연속성 (gauge 미분가능성)
n_grav 공식 (GR)
Spontaneous breaking 도메인 월 (QFT)
```

**정직 원칙 기록:**  "Pattern match ≠ derivation" — 수치 일치한다고
자동으로 정리가 되지 않음.  이 문서는 세션 누적 감사 결과 발견된
모든 예외를 한 곳에 정리.  연구 진행은 이 목록에서 gap 을 고르는
방식으로 (refuted 는 다른 방향 찾고, heuristic 은 formal 유도 시도).
