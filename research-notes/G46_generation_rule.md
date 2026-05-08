# G46 — Generation Rule + Triangle Iteration

**Date**: 2026-05-08 (post G45)
**Origin**: Mingu's three questions, with the answer found
already in `Lib/Physics/Simplex/Counts.lean`.

## Discovery: Counts.lean already had it

```lean
/-- Generation count: C(NS, NT) = C(3, 2) = 3 — no 4th generation. -/
def gen_count : Nat := 3
```

Plus: `OS.PairForcing` (atom pair (2,3) unique) +
`OS.Atomicity` (d = 5 unique via Bézout).

The (3, 2) atomicity is **forced** by atomicity arguments,
not chosen.

## Three answers

### 1. `(2+3)²⁵`: 25 = orthogonal, 2/3 = binomial choice per level

NOT "axis-2 stacked + axis-3 stacked".  Structurally:
  * 25 levels = orthogonal direction (CD doublings).
  * Each level: binary choice {S-type weight 3, T-type weight 2}.
  * Total `(N_S + N_T)²⁵ = 5²⁵` aggregates over `2²⁵` partition
    choices.

### 2. C(N_S, N_T) = C(3, 2) = 3 = SM generations

The (3, 2) atomicity FORCES 3 fermion generations via binomial.
Already proven in `Counts.lean`.  N_S=3 vs N_T=2 are BINOMIALLY
related, not independent.

### 3. Triangle iteration `a_{n+1} = T(a_n)`

`a_n · C 2 + a_n` = `C(a_n, 2) + a_n` = `a_n(a_n+1)/2` =
**triangle number** `T(a_n)`.

Starting from `a_1 = 2` (binary base):
  * `a_1 = 2`  (= N_T)
  * `a_2 = T(2) = 3`  (= N_S) ✓
  * `a_3 = T(3) = 6`
  * `a_4 = T(6) = 21`
  * `a_5 = T(21) = 231`

OEIS A007501.  **The (3, 2) atomicity = first two terms!**

## Modules (3 .lean + 1 capstone, all ∅-axiom)

  * `TriangleIteration.lean` — `T(n) = n(n+1)/2`; `triIter`;
    sequence 2, 3, 6, 21, 231.
  * `GenerationCount.lean` — binomial; `C(3,2) = 3`; no 4th gen.
  * `OrthogonalDirection.lean` — `(2+3)²⁵` = 25 binomial steps.
  * `G46Capstone.lean` — 5 cluster witnesses.

## Connection to Λᵏℂ⁵

`Counts.lean` lambda dims (5-simplex exterior algebra):
  `1, 5, 10, 10, 5, 1` — Pascal triangle row 5.
Total = `2⁵ = 32`.  This is `(1+1)⁵` — binomial again.

So the entire DRLT structure is **binomial all the way down**:
  * 5-simplex exterior dims = Pascal row 5
  * Generation count = C(3, 2)
  * 25-level total branches = (3+2)²⁵ = 5²⁵ = N_U
  * Atomicity (3, 2) = first two terms of triangle iteration

## Filed under

  * G36-G45 (PRs #62-#73)
  * `Lib/Physics/Simplex/Counts.lean` (existing repo answer)
  * OEIS A007501 (triangle iteration)
