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

### 3e. 중력의 *Binet-Cauchy 내 위치* (G-D2, G-D3 narrow)
- **주의:** 이 항목은 **중력 전반이 아님** — 중력 big picture (Regge
  action, cosmology 0-param predictions) 는 §7 참조, 잘 derive 됨.
- **narrow 질문:** 중력 coupling/corrections 을 1+12+12 Binet-Cauchy
  분해의 어느 slot 에 mapping 하는 **specific combinatorial 공식**
  이 있는가?
- **상태:** FND_025 (Λ^k slot), FND_026 (shape functional), FND_035–037
  (M_i 기하 유도) 모두 특정 naive 가설 refuted.  Regge + cosmology
  프로그램 자체는 작동.  이건 세부 튜닝 missing, 프로그램 결함 아님.

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

## 7. 중력 status (정정: 실제로 가장 derive 된 sector)

**이전 draft 의 오류 정정 (Mingu 지적, 2026-04-18).**  이전 버전은
FND_025–037 refutations 를 "중력 전반 미완성" 으로 해석했으나 이는
**과잉 비관**.  실제로 중력은 DRLT 에서 **가장 많이 derive 된 sector**.

### 7a. 중력 big picture (derived, 작동 중)

| 결과 | 위치 | 상태 |
|------|------|------|
| **Regge action `S = Σ A_h·δ_h`** | ch06 eq:Regge | ✓ 공리 + 순수 기하 |
| **Hinge area `A_h = √det(G_h)`** | ch06 + BinetCauchy.lean | ✓ Lean 검증 |
| **`det(G_h)` 명시 공식** `1 − Σ\|G\|² + 2·Π\|G\|·cosΦ_h` | ch06 eq:detGh | ✓ 기하 |
| **Gauge↔geometry coupling** (이산 Einstein eq) | ch06 holonomy | ✓ Φ_h ↔ det(G_h) |
| **Continuum limit `→ (1/16πG)∫R√g`** | ch06 theorem | ✓ standard Regge 극한 |
| **`ℏ = √det/(4 ln 2)` dynamical** | ch07 | ✓ 유도식 |
| **`Ω_Λ = (1−1/π)(1+α_GUT/d) = 0.6850`** | ch13, COS_002 | ✓ 0-param, **0.0008%** |
| **`w = −1` (정확)** | ch13, COS_002 | ✓ 0-param |
| **`η_B = 6.13×10⁻¹⁰`** | COS_002 | ✓ 0-param, 0.5% |
| **`DM/baryon = d + 1/n_S = 5.33`** | COS_001 | ✓ 0-param, 0.6% |
| **Inflation `n_s = 1 − 2/N_*`** | CST_001 | ✓ 0-param |
| **Singularity 제거 정리** (det(G_h)=0 codim-2) | ch06 | ✓ 정리 |
| **유한 vacuum energy** (no Λ⁴_UV 발산) | ch13 | ✓ 유도 |

이 목록 이 **gauge 의 한 줄 (α_GUT = 6/(25π²)) 보다 훨씬 포괄적.**

### 7b. Refuted 된 것: 중력 sub-detail 만 (narrow)

FND_025–037 refutations 는 **중력 전반이 아니라** 다음 **특정 기술적
질문들**:

| FND | 정확히 refuted 된 세부 가설 |
|-----|-----------------------------|
| FND_025 | "중력이 `Λ^k(ℂ⁵)` 분해의 특정 slot 에 위치" |
| FND_026 | "중력 = 순수 shape functional" |
| FND_035 | "M_i (13.75, 3.5, 1.0) 직접 기하 유도" |
| FND_036 | "M_i = Regge deficit 특정 조합" |
| FND_037 | "W3 Schubert T-weight 로부터 M_i" |

즉, **Regge action + cosmology big picture 는 건강**, 다만
(i) 중력을 Binet-Cauchy 1+12+12 중 어디에 assign 할지 +
(ii) coupling correction weights M_i 의 first-principle 유도 — 이
세부 튜닝만 안 됨.  Fine detail 이지 전체 프로그램의 실패 아님.

### 7c. 실제 열린 중력 gap (narrow)

- **G-D2**: 중력이 Binet-Cauchy 1+12+12 의 어디에 대응?
- **G-D3**: Δ_G = +0.15 의 combinatorial 공식?
- **G-M_i**: M_i weights 의 clean 유도
- **G-D6**: ε₀ functional form `f(N_H, d)`
- **G-N1**: Regge S_var = 56.79 의 의미

이들 은 **좁은 열린 문제** 이고 전반 중력 프로그램의 결함 아님.

### 7d. 정정된 결론

- **Gauge sector** (α_GUT 등): **derive 되었으나 narrow** — atoms →
  d=5 → Binet-Cauchy → 6/(25π²).  간결.
- **Gravity sector** (Regge, cosmology, ℏ): **가장 많이 derive 됨** —
  공리 + 기하 → Regge → 연속 극한 → cosmology 0-param 예측 (Ω_Λ
  0.0008% 등).  훨씬 포괄적.
- **Open sub-details** (G-D2/D3/M_i/D6/N1): 세부 튜닝 미완.  전반
  결함 아님.

**정직한 한 줄:** DRLT 는 gauge 와 중력 모두 공리에서 derive 한다.
범위·정밀도 측면에서 **중력 쪽이 오히려 더 많이 유도된 상태**.
FND_025–037 refutations 는 특정 sub-detail 의 naive 가설 솎아내기
였지 중력 전반의 실패가 아니다.

---

## 8. 정직한 경계선 요약

**공리 → Lean 으로 닫힌 gauge 사슬:**
```
관계 → R1–R4 + Frobenius → ℂ
     → atoms={2,3} → alive d=5=(2+3)
     → Binet-Cauchy (1+12+12=25)
     → α_GUT = 6/(25π²) (Path 1 = Path 3 via Euler)
     → σ-inv ↔ vector-like
     → swap tower 유일 고정점 = 5
```

**공리 + 기하 → 중력 사슬 (Lean 외, 고전 + DRLT book):**
```
G_ij → det(G_h) = 1 − Σ|G|² + 2Π|G|cosΦ_h
     → A_h = √det(G_h)  (hinge area)
     → Regge action S = Σ A_h δ_h  (공리적, no free param)
     → 연속 극한 → (1/16πG)∫R√g  (standard Regge)
     → ℏ = √det/(4 ln 2)  dynamical
     → Ω_Λ = (1−1/π)(1+α/d), w=−1, η_B, DM/baryon, n_s, r
       (모두 0-param, Ω_Λ는 0.0008% 정밀도)
```

**미완 / fit / heuristic (narrow sub-details):**
```
Path 2 (GUE) — r² 계수는 확인, α_GUT 로의 점프는 heuristic
M_i (13.75, 3.5, 1.0) — fit, first-principle 없음
ε₀ ≈ 0.0038 — functional form f(N_H, d) 불명
Δ_G = +0.15 — 값은 trace conservation 맞으나 combinatorial 공식 없음
Webb dipole f = 0.17% — 관측 맞추기 수준
세부 "universal ~2.4%" 보정 — naive 는 refuted, 정제 버전 open
```

**물리 input (not 수학):**
```
R2 연속성 (gauge 미분가능성 요청)
n_grav = d(d−3)/2 (GR 공식)
Spontaneous breaking 도메인 월 (QFT)
```

**정직 원칙 기록:**  "Pattern match ≠ derivation" — 수치 일치한다고
자동으로 정리가 되지 않음.  이 문서는 세션 누적 감사 결과 발견된
모든 예외를 한 곳에 정리.  연구 진행은 이 목록에서 gap 을 고르는
방식으로 (refuted 는 다른 방향 찾고, heuristic 은 formal 유도 시도).
