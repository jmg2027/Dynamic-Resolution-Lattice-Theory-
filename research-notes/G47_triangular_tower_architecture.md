# G47 — Triangular Tower Architecture

**Date**: 2026-05-08 (post G46)
**Origin**: Mingu's three-part synthesis.

## The unifying picture

The 25-level CD tower is a **narrowing triangular building**:
  * Each floor = 5-simplex slice (3 S + 2 T = 5 vertices)
  * Higher floors NARROWER (fewer surviving properties)
  * Bottom (Cut substrate) bears the load
  * Top (level 25) pointiest (only Z/2 + norm + N_U)

## Three new insights

### 1. Narrowing tower

| Level | Lost | Surviving |
|---|---|---|
| 0 | — | 5 |
| 1 | ordering | 4 |
| 2 | commutativity | 3 |
| 3 | associativity | 2 |
| 4 | alternativity | 1 |
| 5+ | pow-assoc | 0 |

### 2. Optimal precision per level (NEW)

In `(3+2)²⁵ = Σ C(25,k)·3^k·2^(25-k)`, each level n has
optimal k=n preserving all properties at that level.

Loss = **mismatch with optimal k**, not unavoidable.

### 3. 3-axis absorbs (KEY reframing)

> "2가 잃는게 아니라 3이 가져가는것"

Properties don't vanish — **3-axis absorbs them**:

| Level | Absorbed by 3-axis |
|---|---|
| 0 | 0 |
| 1 | 1 (ordering) |
| 2 | 2 (+comm) |
| 3 | 3 (+assoc) |
| 4 | 4 (+alt) |
| 5+ | 5 (saturated) |

2-axis carries **binary doubling force only**; everything else
absorbed by 3-axis.

## ℝ as squashed projection

ZFC ℝ = **level-1 substrate carrying 23 hidden 3-axes** (one
per level above level 2).  Continuity, completeness, density
are all **absorbed 3-axis features from higher levels**.

## Modules (4 .lean + 1 capstone, all ∅-axiom)

  * `PropertySurvival.lean` — 5→4→3→2→1→0
  * `OptimalPrecision.lean` — optimal k=n per level
  * `RealAsSquashed.lean` — 23 hidden axes
  * `AbsorbedByThree.lean` — 0→1→2→3→4→5 absorption
  * `G47Capstone.lean` — 5 cluster witnesses

## Synthesis

The 25-level CD tower is a **mutually-generative bipartite
fractal**:
  * 2-axis = verb (binary force, doubling)
  * 3-axis = noun (info capacity, absorbs)
  * 25 levels = orthogonal stack
  * (3+2)²⁵ = 5²⁵ = N_U total branches
  * Apex residual = DRLT physics substrate

## Filed under

  * G36-G46 (PRs #62-#74)
  * `Lib/Physics/Simplex/Counts.lean`
