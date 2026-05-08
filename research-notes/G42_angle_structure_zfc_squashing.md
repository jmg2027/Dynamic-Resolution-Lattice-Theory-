# G42 — 90° Truth, 180° Illusion, 45° Gauge

**Date**: 2026-05-08 (post G41 / PR #69)
**Origin**: Mingu's three-part angle insight.

## Three insights

### 1. 180° is illusion, 90° is truth

ZFC: `+3` and `−3` are 180° opposites on a 1D line.
213: `SignedCut := Cut × Cut` is a 2D plane; `(3, 0)` and
`(0, 3)` are at **90°** (orthogonal).

Negative is NOT going backward — it's a sideways move into an
**independent vertical dimension**.

### 2. 45° gauge diagonal — squashing kernel

`(c, c)` diagonal = gauge freedom (vacuum).  ZFC projects 2D
plane along orthogonal-to-diagonal, squashing 2D → 1D.  Genuine
90° Y-axis appears as "180° opposite" only after squashing.

### 3. Doubling fractal — mechanical 90° extension

Each CD level adds ONE 90°-orthogonal axis: 1 → 2 → 4 → 8 →
... → 2²⁵.

| Level | Dim | ZFC name |
|---|---|---|
| 0 | 1 | ℝ⁺ (Bishop magnitude) |
| 1 | 2 | ℝ (squashed from 2D) |
| 2 | 4 | ℂ (squashed from 4D) |
| 3 | 8 | ℍ |
| 4 | 16 | 𝕆 |
| 25 | 2²⁵ | substrate ceiling |

ZFC squashes intermediate levels via gauge projection.

## Angle = 360°/order

| Rule | `(0,1)²` | order | Angle |
|---|---|---|---|
| sign | `(1, 0) = +1` | 2 | **180°** |
| complex | `(−1, 0) = −1` | 4 | **90°** |
| quaternion (per axis) | `−1` | 4 | 90° |

**Same pair shape, different mul rule → different order →
different angle label.**

## Modules (4 .lean + 1 capstone, all ∅-axiom)

  * `SharedPairSlot.lean` — same `(0,1)`, different square
  * `RotationOrder.lean` — angle = 360/order formulas
  * `GaugeDiagonal.lean` — 45° gauge = ZFC squash kernel
  * `OrthogonalDoubling.lean` — 1→2→4→...→2²⁵
  * `G42Capstone.lean` — 5 cluster witnesses

## Why this completes the picture

The "negative" mystery — why `(−1)² = +1`? — explained:
  * In 213: `(0,1)·(0,1) = (1,0)` via sign rule's `+ b·d`.
    Order 2.
  * Order 2 → "two flips return" → 180° interpretation.
  * Structurally `(0,1)` is always at orthogonal Y axis,
    never X-flipped.

## Filed under

  * G36-G41 (PRs #62-#69)
