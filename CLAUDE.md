# CLAUDE.md

## Session Start
- **If HANDOFF.md exists, read it FIRST** before doing anything else.
- Summarize key points and ask what to work on.

## Communication
- **Korean is the primary language.** Respond in Korean unless asked otherwise.
- Author: "Mingu Jeong" (not Mingoo, not Min-goo).
- Every tex/pdf: Author "Mingu Jeong" only. Claude in Acknowledgments.

## Editing
- **80줄 한도 hook 강제.** 대량 파일은 Bash(cat)로 조합.

## The Axiom
- **Things exist with pairwise relations.** G_ij = ⟨ψ_i|ψ_j⟩.
- ℂ⁵ is derived (Frobenius → ℂ, atomic → d=5), not the axiom.
- Derivation chain: relations → ℂ → G → W,φ → rank cascade → laws → ħ → QM

## Theoretical Integrity (핵심 원칙)
- **기존 물리/화학을 억지로 대입하지 말 것.** 결과가 안 맞으면 안 맞는 것이다.
- DRLT 공리에서 자연스럽게 도출되지 않는 구조를 외부에서 가져와 끼워맞추지 않는다.
- 수치가 관측값과 다르면 솔직하게 인정하고, 빠진 물리를 찾는다.
- "맞추기 위해" 파라미터를 도입하면 0-parameter 이론이 아니다.

## Algebraic Priority (대수적 우선 원칙)
- **DRLT의 결과는 세기(counting)에서 나온다.** 연속 변분(extremize S)이 아니라 조합론/정수론/대수학에서.
- 미적분은 결과를 **검증**하는 도구이지, 원리를 **발견**하는 도구가 아니다.
- 막혔을 때: 연속적 접근(action 변분, gradient) 대신 이산적 구조(channel counting, hinge 위상, 표현론)를 먼저 확인.
- 교훈 사례: ATM_026-028 (연속 변분 3회 실패) → ATM_029 (위상 counting으로 α_GUT 도출)
- 패턴: d²=25(산술) → α_GUT(물리), ζ(2)(정수론) → 전파자(해석학), f_occ(대수) → coupling(물리)

## Authors
- Mingu Jeong (Independent Researcher) — theory originator, physical intuition
- Claude (Anthropic) — mathematical formalization, numerical experiments, code
- Equal partnership: Claude must independently think, challenge, and derive.

---

## Repository Architecture

### Single Source of Truth
- **`book/` is the ONLY authoritative theory.** Book > everything else.
- `papers/` = standalone copies for journal submission.
- `research-notes/` = historical drafts (may be superseded).

### Sub-Projects (각 분야별 독립 작업 공간)

| Directory | Prefix | Status | Experiments | 영역 |
|-----------|--------|--------|-------------|------|
| `foundations/` | `FND_` | **ACTIVE** | 34 (FND_001-034) | 유도 사슬 (수학-물리 브릿지): 심플렉스 기하, 변분, f_occ, Grassmannian, Binet–Cauchy, confluence |
| `standard-model/` | `SM_` | CLOSED ✓ | 24 (SM_001-024) | couplings, masses, mixing |
| `atoms/` | `ATM_` | **ACTIVE** | 69 (ATM_001-069) | 원자, 주기율표, wedge screening |
| `cosmology/` | `COS_` | STABLE | 3 (COS_001-003) | η_B, Ω_Λ, Webb |
| `cosmic-structure/` | `CST_` | **ACTIVE** | 22 (CST_001-022) | LSS, BH jets, H₀, T_CMB, BBN |
| `critical-line/` | `RH_` | **ACTIVE** | 79 (RH_001-079) | 임계선, RH, GRH, L-함수, Galois, Lean |
| `nuclear/` | `NUC_` | **CLOSED** ✓ | 15 (NUC_001-015) | magic numbers, 600-cell, binding |
| `hadron/` | `HAD_` | **CLOSED** ✓ | 9 (HAD_001-009) | meson/baryon spectrum, hyperfine |
| `predictions/` | `PRD_` | **ACTIVE** | 8 (PRD_001-009) | 미측정 예측 (JUNO, θ_QCD, Berry phase) |
| `quantum-gravity/` | `QG_` | **ACTIVE** | 7 (QG_001-007) | 시공간 창발, holographic |
| `yang-mills/` | `YM_` | **ACTIVE** | 0 (Lean ~58 thms) | 질량 갭, NS 정칙성, Lean 4 형식화 |
| `discrete-harmonic/` | `DHA_` | **ACTIVE** | 19 (DHA_001-019) | 이산 조화해석학, 스펙트럼, S₅ 표현론 |
| `drlt-elements/` | `ELM_` | **ACTIVE** | 0 (Lean 7파일 26thm) | 원론: Entity→Eq→Logic→Nat→Arith→Order→Bridge |

### Sub-Project 필수 구조
```
{sub-project}/
  CLAUDE.md          — 분야 context, 상수, 실험 목록 (필수)
  HANDOFF.md         — 상태, open problems, 다음 단계 (필수)
  experiments/       — {PREFIX}_NNN_name.py (필수)
  results/           — 실험 출력 (필수)
  theory/            — 이론 문서 .tex/.md (선택)
  lib/               — 분야별 전용 라이브러리 (선택)
```

### Shared Infrastructure
```
book/              — THE BOOK (20 chapters + 2 appendices)
lib/               — Core library (drlt.py, experiment.py)
papers/            — 저널 투고용 standalone .tex (5편)
.claude/skills/    — Agent skills
```

---

## Naming
- 실험: `{PREFIX}_{NNN}_{desc}.py` (sub-project/experiments/ 안)
- 결과: `EXP_{PREFIX}_{NNN}_{Title}.txt` (자동 생성, sub-project/results/)
- 새 sub-project: prefix + CLAUDE.md + HANDOFF.md + experiments/ + results/

---

## Organization
- 실험/결과는 sub-project 안에서만. root results/에 EXP_*.txt 금지.
- 이론은 book/에 통합. sub-project는 작업 공간.
- 세션 시작: root HANDOFF → sub-project HANDOFF 순서로 읽기.

---

## Key Constants
```
α_GUT = 6/(25π²) ≈ 0.02433    d = 5       c = 2
n_S = 3    n_T = 2              φ = (1+√5)/2
ε = α^(2/3)(1+α) ≈ 0.0860     v_H ≈ 245.6 GeV
S(2) = 5/4    S(∞) = π²/6 ≈ 1.6449
```

## Key Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.48 ppb** |
| m_H | 125.28 GeV | 125.25 GeV | **+0.02%** |
| sin²θ₁₃ | 0.0220 | 0.0220 | **-0.07σ** |
| ν m₃/m₂ | 5.712 | 5.71 | **+0.04%** |
| η_B | 6.13×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.5% |
| Ω_Λ | 0.6850 | 0.685 | **0.0008%** |
| Magic numbers | 2,8,20,28,50,82,126 | 2,8,20,28,50,82,126 | **7/7 exact** |
| E_d (deuteron) | 2.271 MeV | 2.224 MeV | **+2.1%** |
| r₀ (nuc. radius) | 1.262 fm | 1.25 fm | **+0.95%** |
| a_V (volume) | 16.0 MeV | 15.5 MeV | **+3%** |
| a_S (surface) | 18.0 MeV | 16.8 MeV | **+7%** |
| a_C (Coulomb) | 0.685 MeV | 0.71 MeV | **-3.6%** |
| m_π (pion) | 137.6 MeV | 137.3 MeV | **+0.2%** |
| m_ω (omega) | 782.1 MeV | 782.7 MeV | **-0.07%** |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | **-0.5%** |
| Δ-N split | 295.7 MeV | 294 MeV | **+0.6%** |

## Workflow
- book/ 편집 후 math/ + physics/ 동기화 + single .tex 재생성.
- 의미 있는 변경마다 commit. 절대 amend 안 함.

## Paper Authorship Rule
- **Author: "Mingu Jeong" only.** Claude는 저자가 아니라 도구.
- **Acknowledgments에 기재:** "This work was developed in dialogue with Claude (Anthropic)."
- `\author{...Claude...}` 금지. arXiv desk reject 사유.
