# Complex 213

**Status**: Closed (4 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

Complex numbers `ℂ` in 213 as `ComplexCut := SignedCut × SignedCut`,
i.e., L2 of the Cayley-Dickson tower on Real213.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Complex/` (4 files)
- **∅-axiom status**: PURE

## Narrative

`ComplexCut := SignedCut × SignedCut` (pair of signed cuts).
Operations as standard complex arithmetic:

```
(a + bi)(c + di) = (ac − bd) + (ad + bc)i
```

realized as `SignedCut`-arithmetic on the components.  No new
substrate primitive (per the SignedCut chapter); ℂ is structurally
the same construction at L2 of the CD tower.

Classical residue theory needed for α_em (G35) C5 reduces to
finite-bracket sums in this representation.

## Connection to other chapters

- `theory/math/signed_cut.md` — L1 base
- `theory/math/cayley_dickson/algebra_tower.md` — L2 of tower
