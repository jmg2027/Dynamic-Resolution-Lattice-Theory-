# Bipartite Decomposition 5 = 3 + 2

**Status**: Closed (4 files, capstone `G44Capstone`).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 — bipartite decomposition → chapter + archive.

## Overview

The atomic dimension **d = 5** decomposes uniquely as **NS + NT = 3 + 2**.
This decomposition is not arbitrary: it's the unique way to split
d = 5 into a bipartite pair where:

- Both parts are atomic primes (no further decomposition)
- The pair satisfies the C2 atomic constants constraint
  (`c · m · n = m² + m + n − 2` at c = 2)
- The ratio NS/NT = 3/2 ties to the algebra-tower asymptote rate

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/BipartiteDecomp/` (4 files)
- **Capstone**: `G44Capstone`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `AdditiveCheck` | Additive decomposition (5 = 3 + 2) check |
| `BinomialExpansion` | Binomial expansion of (1+x)^5 = (1+x)^3 · (1+x)^2 |
| `TernaryBinary` | Ternary × binary decomposition of grade-5 cochain |
| `G44Capstone` | Bipartite-decomposition master |

## Narrative

The split 5 = 3 + 2 is **the** atomic decomposition.  Why not
5 = 4 + 1 or 5 = 5 (irreducible)?

- 5 = 4 + 1: 4 = 2² is composite, not atomic
- 5 = 5: irreducible if we ignore the bipartite axis, but
  213's substrate has TWO axes (NS spatial + NT temporal); the
  pair (NS, NT) = (3, 2) is the unique non-trivial atomic split
  with both parts prime (per C2)

`AdditiveCheck` provides the arithmetic check; `BinomialExpansion`
shows the binomial coefficient row matches the (NS, NT)
factorization; `TernaryBinary` realizes the same split at the
cochain level.

This is the **atomic-numerical** reading of (NS, NT) = (3, 2);
the **structural** reading is in C2 atomic constants chapter
(`theory/physics/foundations/atomic_constants.md`).
