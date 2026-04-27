---
name: catalog-sync
description: "Lean 정리 추가 후 catalogs/ 동기화.  새 atomic 정수, 상수, 결과 → 적절한 catalog 갱신.  Triggered by: '카탈로그 동기화', 'catalog sync', '카탈로그 갱신', 'sync catalogs'."
---

# Catalog Sync

213 도서관 의 3 source (Lean, books, catalogs) 동기화.
Lean = ground truth → catalogs 반영.

## Procedure

### Step 1: 변경된 Lean 파일 식별

```bash
git diff --name-only HEAD~1..HEAD lean/E213/ | head
```

### Step 2: 새 정리 추출

각 변경 파일에서 새 theorem 식별:
- `theorem`, `def`, `class` 선언
- 결과 정수 (`= N` 형태)
- atomic 표현 (NS, NT, d 사용)

### Step 3: 적절한 catalog 매핑

| 새 결과 | 갱신 catalog |
|---|---|
| 새 atomic 정수 | catalogs/atomic-integers.md |
| 물리 상수 chain | catalogs/physics-constants.md |
| 원소 / Z atomic | catalogs/periodic-table.md |
| 측정 결판 | catalogs/falsifiers.md |
| Multi-output 정수 | catalogs/correspondences.md |
| 수학 정리 | catalogs/math-theorems.md |

### Step 4: catalog 항목 추가

각 새 결과:
```markdown
  N = atomic_form  (file_path:line, 정밀도)
```

### Step 5: 책 갱신 권장 (선택)

해당 분야 books/<track>/<field>.md narrative 도 동기화 권장.

## 사용 시점

- 마라톤 종료 시
- 새 결과 commit 직후
- HANDOFF 작성 전
- Migration 후

## 일관성 원칙

  Lean = ground truth (build + decide)
  Catalogs = lookup
  Books = narrative

  세 source 동기화 유지.
