# CLAUDE.md

## Session Start
- **If HANDOFF.md exists, read it FIRST** before doing anything else.
- Summarize key points and ask what to work on.

## Communication
- **Korean is the primary language.** Respond in Korean unless asked otherwise.
- Author: "Mingu Jeong" (not Mingoo, not Min-goo).
- Every tex/pdf: "Joint research by Mingu Jeong and Claude (Anthropic)"

## Editing Rules (1원칙: 청크)
- **새 파일 작성 시 100줄 이하 청크로 나눠 Write → Edit 반복.** 절대 한번에 200줄 이상 쓰지 않는다.
- Edit files in small chunks. Never write an entire large file at once.
- Use Edit tool for incremental changes, not Write for full rewrites.

## The Axiom
- **Things exist with pairwise relations.** G_ij = ⟨ψ_i|ψ_j⟩.
- ℂ⁵ is derived (Frobenius → ℂ, atomic → d=5), not the axiom.
- Derivation chain: relations → ℂ → G → W,φ → rank cascade → laws → ħ → QM

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
| `foundations/` | `FND_` | STABLE | 10 (FND_001-010) | 심플렉스 기하, 변분, f_occ |
| `standard-model/` | `SM_` | CLOSED ✓ | 24 (SM_001-024) | couplings, masses, mixing |
| `atoms/` | `ATM_` | **ACTIVE** | 17 (ATM_001-017) | 원자, 주기율표 |
| `cosmology/` | `COS_` | STABLE | 3 (COS_001-003) | η_B, Ω_Λ, Webb |
| `rh-connection/` | `RH_` | PLATEAU | 7 (RH_001-007) | Riemann Hypothesis |
| `nuclear/` | `NUC_` | NOT STARTED | — | 핵 결합, magic numbers |
| `predictions/` | `PRD_` | NOT STARTED | — | 미측정 예측 (JUNO 등) |
| `quantum-gravity/` | `QG_` | NOT STARTED | — | 시공간 창발, holographic |

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

## Naming Rules

### 실험 파일
```
{PREFIX}_{NNN}_{description}.py
```
- **PREFIX**: sub-project별 고유 (FND, SM, ATM, COS, RH, NUC, PRD, QG)
- **NNN**: sub-project 내 순차 번호 (001부터)
- **description**: snake_case, 실험 내용 요약
- 예: `ATM_014_he_variational.py`, `SM_020_higgs_quartic.py`

### 실험 클래스 내부 ID
```python
class MyExperiment(Experiment):
    ID = "ATM_014"        # PREFIX_NNN
    TITLE = "He Variational Solution"
```

### 결과 파일
```
EXP_{PREFIX}_{NNN}_{Title}.txt
```
실험 실행 시 자동 생성. Title은 실험 TITLE에서 파생.

### 결과 저장 경로 (자동 감지)
`lib/experiment.py`가 결과 저장 경로를 자동 결정:
1. 클래스에 `RESULTS_DIR` 속성 → 그것 사용
2. 실험 파일이 `{sub-project}/experiments/`에 있으면 → `{sub-project}/results/`
3. 위 두 조건 해당 없으면 → root `results/` (fallback)

**수동 RESULTS_DIR 설정 불필요.** `{sub-project}/experiments/`에 넣기만 하면 됨.

### 새 sub-project 생성 시
1. 2-3자 prefix 결정 (기존과 충돌 없이)
2. `{name}/CLAUDE.md` + `{name}/HANDOFF.md` 생성
3. `{name}/experiments/` + `{name}/results/` 디렉토리 생성
4. root CLAUDE.md 테이블에 추가
5. `.claude/skills/{name}/SKILL.md` 생성 (선택)

---

## Organization Rules
1. **새 연구 방향 = 새 sub-project directory.** CLAUDE.md + HANDOFF.md 필수.
2. **실험/결과는 sub-project 안에서만.** root에 실험 파일 두지 않음.
3. **이론은 항상 book/에 통합.** sub-project는 작업 공간일 뿐.
4. **sub-project CLAUDE.md에는 해당 분야 context만.** Agent가 필요한 것만 읽으면 됨.
5. **실험 번호는 sub-project 내 순차.** prefix로 소속 구분.
6. **각 sub-project는 자체 HANDOFF.md 관리.** Root HANDOFF는 요약만.
7. **세션 시작:** root HANDOFF → 작업 sub-project HANDOFF 순서로 읽기.
8. **papers/는 root에 유지.** 저널 투고용. sub-project에서 참조만.
9. **results/는 sub-project 안에만.** root results/는 meta만.

### Paper Classification
| Paper | Sub-Project | Topic |
|-------|------------|-------|
| paper1 | foundations | chiral decomposition (why ℂ, d=5) |
| paper2 | foundations | Frobenius → gauge group |
| paper3 | standard-model | zero-parameter predictions |
| paper4 | standard-model | zeta spectral dim, β-function |
| paper5 | rh-connection | Born-rule Gram graphs, critical line |

---

## Book Structure
```
book/chapters/
  ch01-03: Part I   — Foundations (why ℂ, why d=5, uniqueness)
  ch04-05: Part II  — Simplex Geometry (combinatorics, theorems)
  ch06-08: Part III — Physics Emergence (metric, ħ, couplings)
  ch09-11: Part IV  — Matter (masses, atoms, mixing)
  ch12-14: Part V   — Completeness (ghosts, cosmology, block)
  ch15-20: Part VI  — Applications (YM, stars, QCD, hydrogen)
  ch21:    Appendix  — Occupation fraction + Higgs quartic
```

## Key Constants
```
α_GUT = 6/(25π²) ≈ 0.02433    d = 5       c = 2
n_S = 3    n_T = 2              φ = (1+√5)/2
ε = α^(2/3)(1+α) ≈ 0.0860     v_H ≈ 245.8 GeV
S(2) = 5/4    S(∞) = π²/6 ≈ 1.6449
```

## Key Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.7 ppb** |
| m_H | 125.28 GeV | 125.25 GeV | **+0.02%** |
| sin²θ₁₃ | 0.0220 | 0.0220 | **-0.07σ** |
| ν m₃/m₂ | 5.712 | 5.71 | **+0.04%** |
| η_B | 6.10×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.04% |

## Resolved Problems (All 5 original SM open problems closed)
1. ~~Higgs mass~~ → +0.02% via face BC + embedding (SM_020/021)
2. ~~Δm_np~~ → -1.5% via EM excess fraction (SM_022)
3. ~~1/α₂~~ → phantom problem (ch08 already solved)
4. ~~Neutrino ratio~~ → +0.04% via T₂₃ Basel correction (SM_023)
5. ~~1st gen quarks~~ → Ξ_confined = α/(d²-1) only (SM_024)

## Workflow Rules

### Book Edits
1. All theory → `book/chapters/*.tex`. Small incremental edits.
2. After edits, regenerate `drlt_book_single.tex`.
3. Papers in `papers/` — update only when submitting.

### New Research Direction
1. Create `{topic}/` directory with CLAUDE.md + HANDOFF.md.
2. Choose unique 2-3 char prefix. Add to root CLAUDE.md table.
3. Put experiments, results, theory documents inside.
4. Once results are solid, integrate into book.

### Git
- Commit after each meaningful change.
- Push to designated branch. Never amend.
- Sub-projects can use feature branches.
