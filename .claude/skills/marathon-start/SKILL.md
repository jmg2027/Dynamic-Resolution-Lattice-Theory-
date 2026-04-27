---
name: marathon-start
description: "Blueprint 따라 새 마라톤 시작.  blueprints/{math,physics}/<field>.md 정독 + Phase 계획 시작.  Triggered by: '마라톤 시작', 'marathon start', 'start blueprint', 'begin field'."
---

# Marathon Start

213 도서관 의 새 분야 마라톤 진입.  blueprints/ 의 14+14 분야
중 하나 따라 진행.

## Procedure

### Step 1: 분야 선택

사용자 요청 또는 우선순위 따라:

```
blueprints/math/INDEX.md      14 수학 분야
blueprints/physics/INDEX.md   14 물리 분야
```

★★★ 최우선 후보:
- math/01 Probability, math/02 Multivariable, math/03 Topology
- math/10 Combinatorics, math/13 213 Meta
- physics/01 Atomic, physics/02 Hadron, physics/04 Cosmology
- physics/07 Yang-Mills, physics/10 Falsifier

### Step 2: Blueprint 정독

선택된 `blueprints/<track>/<NN>_<field>_213.md`:

1. *왜 이 분야* — ZFC 접근 의 고통점
2. *213-native 등장* — 자연 derivation 경로
3. *이미 깔린 빌딩 블록* — 시작점
4. *Phase 계획* — 구체 단계
5. *다른 트랙 연결*
6. *미해결 문제*

### Step 3: 첫 Phase 시작

Phase 명명: `<Track><NN>` (Phase D 다음 = E, F, ...).

각 Phase:
- 단일 Lean 파일 (~80 줄)
- decide-checked theorems
- doc-string 명시 (왜 이 결과가 atomic)

### Step 4: 새 디렉토리 생성

```
lean/E213/<Math|Physics>/<Field>/
  Phase<NN>_<topic>.lean
  ...
  Capstone.lean    (분야 종합)
```

### Step 5: 진행 종료 시 (마라톤 끝)

1. lake-build-verify 실행
2. purity-check 실행
3. catalog-sync 실행
4. books/<track>/<field>.md 작성
5. handoff 갱신

## 사용 예

```
사용자: "Probability 213 마라톤 시작"
→ blueprints/math/01_probability_213.md 정독
→ lean/E213/Math/Probability/ 생성
→ Phase EA, EB, EC, ... 진행
→ 종료 시 4 단계 동기화
```
