---
name: purity-check
description: "DRLT 213 purity 검증 — 0 sorry, 0 외부 axiom, 0 Mathlib import, 0 Classical, 0 native_decide.  Triggered by: 'purity', '순수성', '0 axiom 검증', 'falsifiability check', 'audit purity'."
---

# DRLT 213 Purity Check

CLAUDE.md 의 falsifiability 원칙: Lean 4 core 만 + Raw 공리.
외부 axiom 추가 = *이론 폐기*.

## Procedure

### Step 1: 4 forbidden patterns 검사

```bash
echo "sorry:"
grep -rn "^\s*sorry\b\|:= sorry\|by sorry" lean/E213/ | wc -l

echo "외부 axiom 선언:"
grep -rn "^axiom \|^[[:space:]]*axiom " lean/E213/ | head -5

echo "native_decide:"
grep -rn "native_decide" lean/E213/ | wc -l

echo "Classical / Mathlib:"
grep -rn "open Classical\|import Mathlib" lean/E213/ | wc -l
```

### Step 2: Capstone axioms 점검

핵심 capstone 의 `#print axioms` 검증:

```lean
import E213.Physics.Phase4.Library.CompletePeriodicTable
#print axioms E213.Physics.Phase4.Library.CompletePeriodicTable.all_noble_gas_atomic
-- 기대: [propext, Quot.sound] 또는 axioms not depend
```

### Step 3: 결과 분류

- 4 forbidden 모두 0 + capstone ≤ propext+Quot.sound → ✅ pure
- 어느 하나 위반 → ⚠️ 위반 위치 보고 + 수정 제안
- 외부 axiom 발견 → ★ 즉시 보고 (이론 폐기 trigger)

### Step 4: Fix 제안

위반 시:
- sorry → 정리 다른 방법 또는 제거
- Mathlib import → 213-native 함수 작성
- Classical → constructive 증명
- native_decide → decide 또는 명시적 증명

## 사용 시점

- Commit 전 강제 점검
- 마라톤 종료 시
- Migration 후
- 의심스러운 외부 import 추가 시
