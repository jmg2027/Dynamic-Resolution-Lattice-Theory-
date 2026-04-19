# DRLT 재작업 필요 분야 분류

**Date:** 2026-04-19
**기반:** `application_traversal.md` + `audit_framework.md` +
closed derivation chain.
**목적:** 닫힌 공리 체인 관점에서 각 물리 영역을 4 tier 로 분류.

---

## 분류 기준

| Tier | 상태 | 필요 작업 | 시간 |
|------|------|-----------|------|
| **A: Maintain** | closed chain 과 **이미 정합** | step tag 달기 정도 | 소 |
| **B: Polish** | 큰 그림 ✓ but narrow gap 존재 | edit-level 개선 | 중 |
| **C: Rework** | heuristic 구조 있어 **재정리 필요** | 공식 재유도 | 대 |
| **D: Rebuild** | 외부 recipe/fit 로 **뼈대 교체** | 이론 구조 교체 | 특 |

---

## Book chapter 분류

### Tier A: Maintain (10)
- **ch01** (Why ℂ) — Frobenius + Aut=ℤ/2 rigorous (Step 6)
- **ch02** (Why d=5) — atoms={2,3} Lean 검증 (Step 7)
- **ch03** (rep uniqueness) — α_GUT = 1/(d²ζ(2)) rigorous (Step 7-8)
- **ch04** (simplex geometry) — 조합 기하 rigorous (Step 8)
- **ch05** (variational) — δ=π, det=2/3, c=2 algebraic proof (Step 8)
- **ch17** (Webb dipole) — Step 13 decisive signature, 유지 그대로
- **ch19** (QCD) — confinement + Λ_QCD + η/s CLOSED
- **ch20** (hydrogen) — IE 13.606 exact
- **ch21** (occupation) — m_H 0.02%
- **ch22** (213) — 1줄 axiom + 9 property Lean (클린업 완료)

### Tier B: Polish (8)
- **ch06** (geometry) — Lorentz/ADM/LLN narrow heuristic 서술 개선
- **ch07** (ℏ) — 4 ln 2 분해 서술 + path integral postulate 명시
- **ch08** (couplings) — Path 2 GUE heuristic, β-function 서술 보강
- **ch09** (masses) — v_H/m_τ heuristic 서술 보강
- **ch13** (cosmology) — summary table 동기화, N_* 공식 재유도
- **ch14** (block) — ε₀(x) Webb 연결 explicit
- **ch16** (compact stars) — η/s Step 9 residue 유도 명시
- **ch18** (path integral) — level-by-level pattern count 공식화

### Tier C: Rework (2)
- **ch11** (mixing) — w=3/(5π) 는 rigorous, CKM Wolfenstein λ/A/ρ̄/η̄
  의 closed form 은 heuristic.  `n_S=3 × 5-vertex` 세대 구조 재유도.
- **ch12** (ghosts) — Σ Δ_i = 0 rigorous but ε₀/M_i 는 fit.  Step 13
  lens framework 로 ghost 재정의 (BRST = lens coherence).

### Tier C/D 경계: YM
- **ch15** (YM) — 1050줄 18 thm + Lean 58 thm, deep-audit 미완.
  closed chain 관점 "mass gap = discrete hinge spectrum" 으로
  재정리 필요 (Rework 급).  Clay millennium 스케일 때문에
  별도 track 으로 분리 고려.

---

## Sub-project 분류

### Tier A: Maintain (4)
- **foundations/** (FND_001–041) — closed chain 기반, 클린 상태
- **standard-model/** (SM_001–024) — CLOSED ✓, Ξ_conf 내재
- **nuclear/** (NUC_001–015) — Magic 7/7 exact, CLOSED ✓
- **hadron/** (HAD_001–009) — 주요 정밀 결과 강 (m_π 0.2%, Δ-N 0.6%)

### Tier B: Polish (3)
- **cosmology/** (COS_001–003) — ch13 backup, COS_004 (JUNO) 추가 고려
- **cosmic-structure/** (CST_001–022) — LSS 10/68 미완, H₀ tension 정량화
- **quantum-gravity/** (QG_001–007) — ch06/07/14/18 과 overlap 정리

### Tier C: Rework (1)
- **predictions/** (PRD_001–009) — "step refute signature" 로 reframe.
  각 예측에 closed chain step tag 추가.

### Tier D: Rebuild (1)
- **atoms/** (ATM_001–069) — H/He 유지, Z ≥ 3 는 **σ_recipe 제거**
  후 **fractal simplex framework** (multi-electron simplex) 로 rebuild.
  `atoms/theory/multi_electron_simplex_framework.md` §16 기반.
  G-ATM (multi-simplex solver) 해결이 전제.

### 분류 보류 (순수 수학, 이번 범위 밖)
- **critical-line/** (RH_001–079) — RH/GRH/L-함수
- **yang-mills/** — Lean ~58 thms, Clay scale
- **discrete-harmonic/** (DHA_001–019) — S_5 표현론
- **drlt-elements/** (ELM Lean) — foundational Lean

---

## 요약 표

| Tier | 책 chapter | Sub-project | 합계 |
|------|-----------|-------------|------|
| A: Maintain | 10 (ch01-05, 17, 19-22) | 4 (FND, SM, NUC, HAD) | 14 |
| B: Polish | 8 (ch06-09, 13, 14, 16, 18) | 3 (COS, CST, QG) | 11 |
| C: Rework | 2 (ch11, 12) + YM | 1 (PRD) | 4 |
| D: Rebuild | — | 1 (ATM Z≥3) | 1 |
| 범위 밖 | — | 4 (RH, YM-Lean, DHA, ELM) | 4 |

**총 34 단위 중:**
- **유지 그대로**: 14 (41%)
- **미세 편집**: 11 (32%)
- **구조 재정리**: 4 (12%)
- **뼈대 재구축**: 1 (3%)
- **범위 밖**: 4 (12%)

**72% 가 A+B** (유지 or 편집) — closed chain 이 **대부분 이미 정합**.

---

## 재작업 순서 (우선순위)

### 즉시 (이번 세션 가능)
1. **ch11 (mixing) Rework**: w=3/(5π) 외 CKM Wolfenstein 의
   closed form 유도 시도.  `n_S=3` + `5-vertex period` 조합.
2. **PRD rework**: 각 PRD_NNN header 에 closed chain step tag 추가.

### 중기 (별도 세션)
3. **ch12 (ghosts) Rework**: ε₀ = α/(2π) 재유도 + M_i closed chain.
4. **atoms/ Rebuild**: Z=3 (Li) 을 fractal simplex Level 1 로
   직접 재구성.  σ_recipe 제거.
5. **ch15 (YM) deep-audit**: mass gap = discrete hinge spectrum.

### 장기 (Clay scale)
6. **YM full proof** — Lean 58 thm 통합 + ch15 정리.

---

## 원칙 (재작업 시)

1. **Algebraic Priority**: 연속 변분 아니라 counting 먼저.
2. **기존 물리 억지 대입 금지**: closed chain 에서 자연 유도되면
   채택, 아니면 외부 recipe 쓰지 말고 gap 으로 기록.
3. **Overclaim 금지**: heuristic 은 heuristic 으로 labeling.
4. **Step tag 필수**: 모든 claim 은 closed chain step N 대응.

---

**작성 기록:** 2026-04-19, `claude/review-simplex-swap-y2z6O` 브랜치
에서 `claude/continue-handoff-213-fC38X` 머지 후 작성.
`application_traversal.md` 의 traversal 결과를 4-tier 로 구조화.
