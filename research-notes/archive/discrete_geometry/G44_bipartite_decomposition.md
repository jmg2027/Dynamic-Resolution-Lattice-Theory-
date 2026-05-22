# G44 — Bipartite Decomposition: 5 = 3 + 2

**Date**: 2026-05-08 (post G43)
**Origin**: Mingu's bipartite hypothesis.

## Verdict

| Claim | Status |
|---|---|
| `5 = 3 + 2` (substrate) | ✅ **trivially true** |
| `3²⁵ + 2²⁵ ≈ 5²⁵` | ❌ **off by ~10⁸** |
| `(3+2)²⁵ = 5²⁵` | ✅ **exact (binomial)** |
| Bipartite axes S=3, T=2 | ✅ **aligns with K_{3,2}** |

## Arithmetic

```
3²⁵ = 847,288,609,443
2²⁵ = 33,554,432
3²⁵ + 2²⁵ = 847,322,163,875        (≈ 8.5 × 10¹¹)
5²⁵ = 298,023,223,876,953,125     (≈ 3.0 × 10¹⁷)
ratio ≈ 351 million
```

Pure addition fails.  But binomial expansion exact:

```
(3+2)²⁵ = 5²⁵
       = Σ_{k=0}^{25} C(25, k) · 3^k · 2^(25-k)
```

Each term = partition of 25 doublings into k S-type + (25-k)
T-type.

## Bipartite axes

| Axis | N | Interpretation |
|---|---|---|
| S | 3 | {left, right, halt}; SM 3 generations |
| T | 2 | {0, 1}; {up, down}; {boson, fermion} |

Each CD doubling is EITHER S-type (×3) or T-type (×2).  Total
= `(3+2)²⁵`.

## SU(3) connection

`N_S² − 1 = 8` matches K_{3,2}^{(c=2)}'s `b_1 = 8` matches SU(3)
gauge boson count.  Not coincidence: S-axis cardinality 3 IS
SU(3) color charge structure.

## Refinement of G43

G43 said "vertical 2-adic, horizontal 5-adic".  Deeper:
  * Vertical = T-axis (2-adic)
  * Horizontal = S-axis (3-adic) blended with T
  * Total = `(3+2)²⁵ = 5²⁵` (binomial)

Mingu's 3-component intuition refines simple 5-adic view.

## Modules (3 .lean + 1 capstone, all ∅-axiom)

  * `BipartiteDecomp/AdditiveCheck.lean`
  * `BipartiteDecomp/BinomialExpansion.lean`
  * `BipartiteDecomp/TernaryBinary.lean`
  * `BipartiteDecomp/G44Capstone.lean`

## Filed under

  * G36-G43 (PRs #62-#71)
  * `seed/RESOLUTION_LIMIT_SPEC.md`
