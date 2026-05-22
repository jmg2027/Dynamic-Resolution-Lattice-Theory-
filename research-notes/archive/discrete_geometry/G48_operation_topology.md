# G48 — Operation × Topology

**Date**: 2026-05-08 (post G47)
**Origin**: Mingu's complete synthesis.

## The complete picture

  * **2 = operation** (binary force, doubling)
  * **3 = elements/topology** (information network)
  * Each level: 2의 한 연산 성질을 3의 topology로 표현
  * 25 levels = 25 distinct operational properties
  * Total preservation = 5²⁵ = N_U

## The 25 levels

| Level | Operation | Type |
|---|---|---|
| 1 | + (sign) | sign extension |
| 2 | i (imaginary) | complex |
| 3 | j | non-commutative |
| 4 | k | non-comm cont. |
| 5-7 | e₅..e₇ (octonion) | non-associative |
| 8 | sedenion | zero divisor |
| ... | ... | ... |
| 25 | last | substrate ceiling |

## Why exactly 25?

Two co-saturating constraints:
  * **Algebraic**: CD doubling exhausts at d² = 25
  * **Topological**: 3-axis info saturates at complexity 25

## The two budgets

| Quantity | Value |
|---|---|
| Operation levels | 25 |
| Total complexity sum | 325 (triangular) |
| Per-level atomic states | 5 |
| Total preservation | 5²⁵ = N_U |

## Modules (3 .lean + 1 capstone, all ∅-axiom)

  * `OperationLevels.lean` — 25 cumulative ops
  * `TopologicalComplexity.lean` — monotone, total 325
  * `TotalPreservation.lean` — `5^25 = perLevel ^ levels`
  * `G48Capstone.lean` — 5 cluster witnesses

## Synthesis

```
LEVEL 25 ─── most complex, last property
  ⋮
LEVEL  3 (i, j, k)
LEVEL  2 (imaginary)
LEVEL  1 (+ sign)
─── BASE (Cut, 5 atomic verts)
```

Each level: 3-axis topology expresses ONE 2-operation
property.  25 properties × 5 atomic states = 5²⁵ = N_U.

## Filed under

  * G36-G47 (PRs #62-#75)
  * `Lib/Physics/Simplex/Counts.lean`
