# Directory Structure Proposal — 213 도서관 합의안

**작성**: 수학트랙 (분석학 213 마라톤 완수자) 입장.
**비교 대상**: 물리트랙의 directory 제안.
**목표**: 양 트랙 만족 + CLAUDE.md 정리 원칙 준수 + 미래 확장성.

---

## 1. 핵심 합의점 (양쪽 동의)

✅ **`lean/` 분리** — Lean 코드를 별도 namespace dir
✅ **`Library/` 카탈로그 모듈** — 사용자 진입점 (IELibrary 등)
✅ **`books/` narrative 분리** — paper 와 다른 *읽는 책*
✅ **`catalogs/` lookup tables** — grep-able
✅ **`examples/` Mathlib 스타일** — 사용성 ↑
✅ **`tools/` CLI** — atomic chain 검색

## 2. 차이점 + 합의안

### 2.1 Namespace: `DRLT/` vs `E213/`

**물리**: `DRLT/`
**수학**: `E213/` 유지

**합의**: `E213/` 유지.  근거:
- 80+ commits Lean 모두 import 경로 갱신 (대규모 부작용)
- `DRLT` = 이론 이름, `E213` = Lean 식별자 — 분리 유지
- `lean/E213/` 형식이 명확

### 2.2 옛 코드: `archive/`

**물리**: `archive/` 디렉토리 보존
**수학**: 없음

**합의**: `archive/` 만들지 않음.  근거:
- CLAUDE.md "Deprecated 는 *삭제*"
- "역사적 기록" 가치 = noise
- git history 로 충분

### 2.3 수학 코드 organization

**물리**: `Math/Calculus.lean` 단일
**수학**: `Math/Analysis/`, `Math/Probability/` sub-dirs

**합의**: Sub-dir 채택.  근거:
- 분석학 213 = 176 모듈 — 단일 파일 불가
- 80줄 Lean hook
- 분야별 (probability, multivariable, ...) blueprint 14개 예정
- 각 분야 sub-dir + `_root.lean` umbrella

### 2.4 books 평면 vs 계층

**물리**: 11 chapters 평면
**수학**: `books/math/`, `books/physics/` 계층

**합의**: 계층 채택.  근거:
- 분야 깊이 증가 시 평면 → 혼란
- 분석학 213 만 `ANALYSIS213.md` (370줄) 분리 필요
- 책 다수 → math/ vs physics/ 분리 자연

### 2.5 Seed 디렉토리

**물리**: `axioms/` (AXIOM, PAPER1, ORIGIN, NOTATION)
**수학**: `seed/` (위 + PHILOSOPHY, FALSIFIABILITY)

**합의**: `seed/`.  근거:
- "공리" 만 씨앗 아님 — 철학, 위조가능성 도 씨앗
- AXIOM.md §5.2.1 의 falsifiability 가 핵심 씨앗
- "axioms" 는 너무 좁은 framing

### 2.6 Blueprints (수학트랙 추가)

**물리**: 없음
**수학**: `blueprints/` 추가

**합의**: 채택.  근거:
- 미래 마라톤 14 분야 방향 문서
- 분석학 213 처럼 100% 마라톤 가능한 분야들 명시
- 신규 세션이 어디부터 시작할지 가이드

---

## 3. 최종 합의안 (트리, 1/2)

```
/                               # repo = 213 도서관
├── README.md
├── CATALOG.md                  # ★ master entry
├── INSTALL.md
├── HANDOFF.md
├── CLAUDE.md
├── LICENSE
│
├── seed/                       # ★ 씨앗
│   ├── AXIOM.md
│   ├── ORIGIN.md
│   ├── NOTATION.md
│   ├── PHILOSOPHY.md
│   └── FALSIFIABILITY.md
│
├── lean/                       # ★ Lean 4 formal library
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── E213/
│       ├── Firmware/
│       ├── Hypervisor/
│       ├── OS/
│       ├── App/
│       ├── Meta/
│       ├── Tactic/
│       ├── Infinity/
│       ├── Math/
│       │   ├── Analysis/       # 현재 Real213*
│       │   ├── Probability/    # blueprint 01
│       │   ├── Multivariable/  # blueprint 02
│       │   ├── Topology/       # blueprint 03
│       │   ├── Complex/        # blueprint 04
│       │   ├── Measure/        # blueprint 05
│       │   ├── ODEPDE/         # blueprint 06
│       │   ├── Number/         # blueprint 07
│       │   ├── Functional/     # blueprint 08
│       │   ├── Linear/         # blueprint 09
│       │   ├── Combinatorics/  # blueprint 10
│       │   ├── Group/          # blueprint 11
│       │   ├── Information/    # blueprint 12
│       │   ├── Logic/          # blueprint 14
│       │   └── _root.lean
│       ├── Physics/
│       │   ├── Foundation/
│       │   ├── Constants/
│       │   ├── Particles/
│       │   ├── Atoms/
│       │   ├── Nuclear/
│       │   ├── Hadron/
│       │   ├── Cosmology/
│       │   ├── YangMills/
│       │   └── _root.lean
│       └── Library/            # ★ 카탈로그 모듈
│           ├── IELibrary.lean
│           ├── CouplingLibrary.lean
│           └── ... (28+)
```

## 트리 (2/2)

```
├── papers/                     # 저널 .tex 평면
│   ├── analysis213.tex
│   ├── physics213.tex
│   └── architecture213.tex
│
├── books/                      # ★ narrative 계층
│   ├── README.md
│   ├── 00-overview.md
│   ├── math/
│   │   ├── analysis213.md
│   │   ├── probability213.md
│   │   └── ...
│   └── physics/
│       ├── periodic-table.md
│       ├── particle.md
│       └── ...
│
├── catalogs/                   # ★ lookup tables
│   ├── README.md
│   ├── atomic-integers.md
│   ├── physics-constants.md
│   ├── periodic-table.md
│   ├── correspondences.md
│   ├── falsifiers.md
│   ├── lemma-index.md
│   ├── math-theorems.md        # ★ 수학트랙 추가
│   └── modules.md              # ★ Lean 모듈 → 정리 매핑
│
├── blueprints/                 # ★ 미래 마라톤 방향
│   ├── INDEX.md
│   ├── 00_DIRECTORY_PROPOSAL.md  (이 파일)
│   ├── 01_probability_213.md
│   ├── 02_multivariable_213.md
│   └── ... (14 분야)
│
├── examples/                   # Mathlib 스타일
│   ├── README.md
│   ├── 01-hello-atomic.lean
│   ├── 02-compute-ie.lean
│   ├── 03-verify-prediction.lean
│   ├── 04-atomic-chain.lean
│   ├── 05-import-other-project.lean
│   ├── math-01-mvt.lean        # ★ 수학 예시
│   ├── math-02-integral.lean
│   └── math-03-transcendental.lean
│
├── research-notes/             # 연구 노트 (현 213/research/notes/)
│   ├── 17_existence_mode_lens.md
│   ├── 19_lens_not_functor.md
│   └── ...
│
└── tools/                      # CLI
    ├── lookup_integer.py
    ├── search_constant.py
    └── catalog_grep.sh
```

---

## 4. 마이그레이션 단계

현재 → 합의안 변경 큰 단계 (다음 세션 작업):

### Step 1: seed/ 디렉토리

`213/AXIOM.md`, `ORIGIN.md`, `NOTATION.md` → `seed/`.
PHILOSOPHY.md, FALSIFIABILITY.md 신규 작성.

### Step 2: lean/ 분리

`213/framework/` → `lean/`.  Lakefile + lean-toolchain 이동.
`E213/` namespace 그대로 유지.

### Step 3: lean/E213/Math/ 분야별 sub-dir

현재 `Real213*.lean` 176 모듈 → `Math/Analysis/Real213*.lean`.
이름 유지 (이름 바꾸면 import path 갱신).

### Step 4: books/ 계층

`book/` 평면 → `books/math/`, `books/physics/`.
`ANALYSIS213.md` → `books/math/analysis213.md`.

### Step 5: catalogs/ 신규

`CATALOG213.md` → `catalogs/math-theorems.md` (또는 master로 분리).

### Step 6: blueprints/ 그대로 (이미 작성)

`213/research/blueprints/` → 그대로 유지 또는 root 로 이동.

### Step 7: archive/ 만들지 않음

현재 sub-projects 의 옛 Python experiments 는 *결과만* 213 안에
이전, 옛 Python 자체는 **삭제** (git history 보존).

---

## 5. 핵심 원칙

| 원칙 | 출처 |
|---|---|
| Deprecated 는 삭제 | CLAUDE.md |
| 80줄 hook | 강제 |
| 자연스러운 reading order | CLAUDE.md |
| 외부 axiom 추가 = 이론 폐기 | AXIOM.md §5.2.1 |
| 0 sorry, axioms ≤ {propext, Quot.sound} | 형식 검증 기준 |
| Mathlib-free | Lean 4 core only |

이 6 원칙은 디렉토리 변경에서도 *유지*.

---

## 6. 결론

**70% 합의** (Library 모듈, examples, tools, catalogs, books 분리).
**30% 차이** (namespace, archive, math sub-dir, books 계층, seed 명명).

수학트랙 입장에서 합의안이 양쪽 더 공평 + 미래 확장성 ↑.

물리트랙의 검토 + 사용자 결정 대기.

