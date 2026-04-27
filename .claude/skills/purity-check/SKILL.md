---
name: purity-check
description: "DRLT 213 purity verification — 0 sorry, 0 external axiom, 0 Mathlib import, 0 Classical, 0 native_decide.  Triggered by: 'purity', '순수성' / 'purity', '0 axiom 검증' / '0 axiom verify', 'falsifiability check', 'audit purity'."
---

# DRLT 213 Purity Check

CLAUDE.md falsifiability principle: Lean 4 core only + raw axioms.
Adding external axioms = *theory abandoned*.

## Procedure

### Step 1: Check 4 forbidden patterns

```bash
echo "sorry:"
grep -rn "^\s*sorry\b\|:= sorry\|by sorry" lean/E213/ | wc -l

echo "external axiom declaration:"
grep -rn "^axiom \|^[[:space:]]*axiom " lean/E213/ | head -5

echo "native_decide:"
grep -rn "native_decide" lean/E213/ | wc -l

echo "Classical / Mathlib:"
grep -rn "open Classical\|import Mathlib" lean/E213/ | wc -l
```

### Step 2: Capstone axioms inspection

Verify `#print axioms` for key capstones:

```lean
import E213.Physics.Phase4.Library.CompletePeriodicTable
#print axioms E213.Physics.Phase4.Library.CompletePeriodicTable.all_noble_gas_atomic
-- expected: [propext, Quot.sound] or axioms not depend
```

### Step 3: Result Classification

- all 4 forbidden = 0 + capstone ≤ propext+Quot.sound → ✅ pure
- any violation → ⚠️ report violation location + suggest fix
- external axiom found → ★ report immediately (theory abandon trigger)

### Step 4: Fix Suggestions

On violation:
- sorry → prove by another method or remove
- Mathlib import → write 213-native function
- Classical → constructive proof
- native_decide → decide or explicit proof

## When to Use

- Mandatory check before commit
- At end of marathon
- After migration
- When suspicious external import is added
