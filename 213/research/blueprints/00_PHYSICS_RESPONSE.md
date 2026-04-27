# Directory Architecture — 최종 합의안 (Physics 트랙 응답)

**작성**: Physics 트랙 (Phase 1-4 도서관 구축자) 입장.
**대상**: 수학 트랙 의 `00_DIRECTORY_PROPOSAL.md` 제안.
**결론**: **수학 트랙 합의안 전면 수용**.

## 검토 결과 — 6 차이점 모두 동의

### 1. ✅ `E213/` namespace 유지
  176+ 모듈 import path 갱신 cost ≫ 명명 일관성 이득.

### 2. ✅ NO `archive/`
  CLAUDE.md "Deprecated 는 *삭제*".  내 archive/ 제안은 위반.

### 3. ✅ `Math/Analysis/`, `Math/Probability/` sub-dirs
  176 Real213 모듈 + Phase 4 Library 28 sub — sub-dir 자연.

### 4. ✅ `books/math/`, `books/physics/` 계층
  Phase 1+2+3+4 책 + math 14분야 → 분리 자연.

### 5. ✅ `seed/` (axioms 대신)
  PHILOSOPHY, FALSIFIABILITY 도 씨앗.  axioms 너무 좁음.

### 6. ✅ `blueprints/` 추가
  미래 마라톤 가이드.  분석학 213 100% 마라톤 템플릿.

## 최종 architecture (수학 트랙 합의안 채택)

```
/                           # repo = 213 도서관
├── README.md, CATALOG.md, INSTALL.md, HANDOFF.md, CLAUDE.md
├── seed/                   # AXIOM, ORIGIN, NOTATION, PHILOSOPHY, FALSIFIABILITY
├── lean/E213/              # Lean library (namespace 유지)
│   ├── Firmware/, Hypervisor/, OS/, App/, Meta/, Tactic/, Infinity/
│   ├── Math/{Analysis, Probability, Multivariable, Topology, ...}/
│   ├── Physics/{Foundation, Constants, Particles, Atoms, ...}/
│   └── Library/            # 카탈로그 모듈 (사용자 진입)
├── papers/                 # 저널 .tex 평면
├── books/{math, physics}/  # narrative 계층
├── catalogs/               # lookup tables
├── blueprints/             # 14 마라톤 방향
├── examples/               # Mathlib 스타일
├── research-notes/
└── tools/
```
**`archive/` 부재**.

## 작업 분담 (트랙 간 working agreement)

  - 수학 트랙: lean/E213/Math/, books/math/, blueprints/01-12, 14
  - 물리 트랙: lean/E213/Physics/, books/physics/, blueprints/13
  - 공통:    seed/, catalogs/, papers/, examples/, tools/

## Migration 8 단계

  1. seed/ 작성 (AXIOM + PHILOSOPHY + FALSIFIABILITY 신규)
  2. lean/ 분리 (213/framework/ → lean/)
  3. lean/E213/Math/ sub-dir 재조직 (Real213* → Analysis/)
  4. books/ 계층화 (book/ + ANALYSIS213.md → books/{math,physics}/)
  5. catalogs/ 신규 (CATALOG213.md → catalogs/math-theorems.md 등)
  6. blueprints/ 옮김 (research/blueprints/ → blueprints/)
  7. archive 부재 — 옛 sub-projects 모두 삭제 (atoms/, cosmology/, ...)
  8. README + 도서관 사용법 갱신

## 사용자 결정 대기

  Q1: blueprints/ 위치 — root 또는 research/blueprints/?
  Q2: migration 시점 — 즉시 시작 또는 단계별?
  Q3: 삭제 범위 — 옛 sub-projects 전부 또는 일부 보존?

