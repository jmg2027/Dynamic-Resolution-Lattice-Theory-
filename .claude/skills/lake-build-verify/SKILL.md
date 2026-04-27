---
name: lake-build-verify
description: "Verify Lean build is clean (E213 namespace).  Run `cd lean && lake build` and report result.  Triggered by: 'build verify', 'lake build', '빌드 확인', 'verify lean'."
---

# Lake Build Verify

Lean E213 빌드 검증.  매 Lean 변경 후 또는 의심스러운 작업 후
실행.

## Procedure

### Step 1: cd lean && lake build

```bash
cd lean && lake build 2>&1 | tail -10
```

### Step 2: Status 분류

- "Build completed successfully." → ✅ clean
- "error:" → ❌ 빌드 실패, 에러 출력 분석
- 경고만 → ⚠️ 경고 수준

### Step 3: 0 sorry 검증

```bash
grep -rn "sorry" lean/E213/ | grep -v "\.lean.olean" | head
```

빈 출력 → ✅ 0 sorry.

### Step 4: 보고

사용자에게 결과:
- "✅ Build clean, 620 modules, 0 sorry"
- 또는 에러 위치 + 제안 fix

## 사용 시점

- Lean 파일 수정 후
- Migration / 디렉토리 변경 후
- Commit 전
- 새 마라톤 종료 시
