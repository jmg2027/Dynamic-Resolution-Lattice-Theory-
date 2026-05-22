# G45 — Cartesian vs Disjoint

**Date**: 2026-05-08 (post G44)
**Origin**: Mingu's "Cartesian product" revision.

## Verdict

> "2^25 × 3^25 = 5^25, 전부 카르테시안 곱"

| Claim | Status |
|---|---|
| `2²⁵ × 3²⁵ = 5²⁵` | ❌ off by ~95× |
| `2²⁵ + 3²⁵ ≈ 5²⁵` | ❌ off by ~10⁸ (G44) |
| `(3+2)²⁵ = 5²⁵` | ✅ exact (G44) |

## Three sandwiched values

```
2²⁵ + 3²⁵   = 847,322,163,875            (~8.5×10¹¹)  too small
5²⁵         = 298,023,223,876,953,125    (~3.0×10¹⁷)  N_U
2²⁵ × 3²⁵   = 28,430,288,029,929,701,376 (~2.8×10¹⁹)  too big
```

Only binomial gives exact.

## Why Cartesian fails

Cartesian `S × T` labels vertices by pairs (s,t) → `|S|·|T| = 6`
labels.  But K_{3,2} is **bipartite** = disjoint union → 5
vertices.

| Operation | Result | Meaning |
|---|---|---|
| Disjoint `S ⊔ T` | 5 | union of verts |
| Cartesian `S × T` | 6 | pairs |
| Power-sum `(|S|+|T|)^n` | 5^n | seqs over union |
| Power-product `|S|^n · |T|^n` | 6^n | seqs over product |

## Conclusion

Only **binomial** `(3+2)²⁵` works.  Three competing decomp:

  * Sum `2²⁵ + 3²⁵`: **way too small** (10⁸× off)
  * Product `2²⁵ · 3²⁵`: **too big** (~95× off)
  * **Binomial `(3+2)²⁵ = 5²⁵`**: **exact**

K_{3,2} is bipartite (disjoint union, 5 verts).  Each of 25
doublings independently picks S-type (factor 3) or T-type
(factor 2).  Total = (3+2)²⁵ via binomial.

## Modules (3 .lean + 1 capstone, all ∅-axiom)

  * `CartesianCheck.lean` — `6²⁵`, sandwich bound
  * `DisjointVsProduct.lean` — 5 vs 6 distinction
  * `G45Capstone.lean` — 5 cluster witnesses

## Filed under

  * G36-G44 (PRs #62-#72)
