# 213 Library Blueprints — Master Index

213 도서관 의 *지도* — 미래 마라톤 + Kernel meta.

## 트랙 별 INDEX

  📋 **Meta Track**    `blueprints/meta/`               (kernel philosophy + phases)
  📐 **Math Track**     `blueprints/math/INDEX.md`       (14 분야)
  ⚛️ **Physics Track** `blueprints/physics/INDEX.md`     (14 분야)

## Meta — 213 Kernel (★★★★ 최우선, KA→KH 완료)

  - `meta/01_213_kernel.md`         비전 + 빌딩 블록 + Phase 개요
  - `meta/01_213_kernel_phases.md`  KB→KH 상세 + 미해결 문제

상태: **101 정리 모두 0 axiom 검증** (`./tools/kernel_regress.sh`).
Lean kernel 의 propext / Quot.sound / Classical.choice 어느 것도
load-bearing 아님 — "Lean = syntactic host, 213 = real foundation"
이 형식적 사실.

## Architecture

  📋 `math/00_DIRECTORY_PROPOSAL.md`  — 수학 트랙 directory 제안
  📋 `physics/00_PHYSICS_RESPONSE.md` — 물리 트랙 응답 (전면 동의)

  최종 architecture 합의:
  - `seed/` (axioms + philosophy + falsifiability)
  - `lean/E213/` (namespace 유지)
  - `lean/E213/Math/{Analysis, Probability, ...}` sub-dirs
  - `lean/E213/Physics/{Foundation, Atoms, ...}` sub-dirs
  - `lean/E213/Library/` 카탈로그 모듈
  - `papers/`, `books/{math,physics}/`, `catalogs/`,
    `examples/`, `blueprints/{math,physics}/`, `tools/`
  - **`archive/` 부재** (CLAUDE.md "deprecated 삭제")

## 작업 분담

  - Math 트랙: lean/E213/Math/, books/math/, math/01-12,14
  - Physics 트랙: lean/E213/Physics/, books/physics/, physics/all
  - 공통: seed/, catalogs/, papers/, examples/, tools/

## 진행 우선순위 (★★★ 최우선)

### Math
- 01 Probability (FluxCut 이미)
- 02 Multivariable
- 03 Topology
- 10 Combinatorics (atomic native)
- 13 213 Meta

### Physics
- 01 Atomic Physics (Phase 4 이미)
- 02 Hadron (m_p 0.000%)
- 03 Nuclear (magic 7/7)
- 04 Cosmology (Ω_Λ 0.0008%)
- 05 Gauge (137 ppm)
- 07 Yang-Mills (Clay)
- 10 Falsifier (CLAUDE.md 기준 2)
- 13 Beyond SM (refutation)

## 사용 방법

새 세션:
1. 위 우선순위 따라 분야 선택
2. blueprint 정독 (Phase 계획 + 빌딩 블록)
3. 마라톤 진행
4. 결과 통합 (Lean + book + catalog)

## 통합 build

```bash
cd lean/
lake build E213
# → 양 트랙 모두 clean, 0 sorry, ≤ propext + Quot.sound
```
