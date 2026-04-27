---
name: lake-build-verify
description: "Verify Lean build is clean (E213 namespace).  Run `cd lean && lake build` and report result.  Triggered by: 'build verify', 'lake build', '빌드 확인' / 'build verify', 'verify lean'."
---

# Lake Build Verify

Lean E213 build verification. Run after every Lean change or
after any suspicious operation.

## Procedure

### Step 1: cd lean && lake build

```bash
cd lean && lake build 2>&1 | tail -10
```

### Step 2: Status Classification

- "Build completed successfully." → ✅ clean
- "error:" → ❌ build failed, analyze error output
- warnings only → ⚠️ warning level

### Step 3: 0 sorry Verification

```bash
grep -rn "sorry" lean/E213/ | grep -v "\.lean.olean" | head
```

Empty output → ✅ 0 sorry.

### Step 4: Report

Report results to user:
- "✅ Build clean, 620 modules, 0 sorry"
- or error location + suggested fix

## When to Use

- After modifying Lean files
- After migration / directory changes
- Before commit
- At the end of a new marathon
