# G41 — Two-Dimensional Number-System Grid (25 × 25)

**Date**: 2026-05-08 (post G40 / PR #68)
**Origin**: Mingu's two-axis insight.

## Core insight

Number-system taxonomy is **2-dimensional**:
  * **Vertical** (CD level, 0..25): algebraic extension.
  * **Horizontal** (FSM grade, 0..25): pattern-recognizability.

Both axes saturate at **index 25** on d=5 substrate.
Total **25 × 25 = 625 cells**.

## Why both axes have 25 levels

d=5 substrate has **N_U = 5²⁵** trajectory branches.  Budget can
be spent on:
  * Algebraic extension: bit-tower `2^n` saturates at n=25.
  * FSM states: factor-of-5 per grade saturates at `5²⁵ = N_U`.

Same substrate, same ceiling.

## The grid

```
                   CD Level →
              0    1    2    3    ...    25
  Grade ↓
   0 (ℕ)    ℕ    ℤ    ℂ_ℤ  ℍ_ℤ   ...   level25_ℤ
   ~12 (ℚ)  ℚ⁺   ℚ    ℂ_ℚ  ℍ_ℚ   ...   level25_ℚ
   ~20      alg⁺ alg  ℂ_alg ...  ...   level25_alg
   25       ℝ⁺   ℝ    ℂ    ℍ     ...   level25 = N_U
   26+      (structurally absent)
```

## Two ceilings coincide

| Quantity | Vertical | Horizontal |
|---|---|---|
| At index 25 | `2^25 ≈ 3.4·10⁷` | `5^25 = N_U` |
| At index 26 | impossible | excess |
| Mechanism | CD doubling | FSM state count |

Both express substrate's **distinguishability budget**.

## Vertical = CD level → algebraic structure

  * 0: positive Bishop reals (Cut)
  * 1: signed reals
  * 2: complex (`i² = -1`)
  * 3: quaternions (loses commutativity)
  * 4: octonions (loses associativity)
  * 5+: sedenions+ (loses alternativity)
  * 25: substrate-maximum

## Horizontal = FSM grade → computational regularity

  * 0: 1 state — constant cuts (ℕ trivials)
  * 1: 5 states — mod-5 patterns
  * 2: 25 states — mod-25 patterns
  * ~5: rationals (small denom)
  * ~12: arbitrary rationals
  * ~20: algebraic with small minimal poly
  * 25: 5²⁵ = N_U FSM states
  * 26+: beyond N_U (structurally absent)

## Modules (3 .lean + 1 capstone, all ∅-axiom)

  * `FSMGradeTaxonomy.lean` — `fsmGradeStates j = 5^j`
  * `HorizontalAxis.lean` — `gradeToType` classifier
  * `TwoDimGrid.lean` — `GridCell`, 25×25 = 625
  * `G41Capstone.lean` — 5 cluster witnesses

## What this completes

| Layer | PR |
|---|---|
| CD vertical (algebraic) | #62-#68 |
| Completeness (ε-δ → modulus) | #68 |
| **2D classification (this)** | **#69** |

Full **2D classification** of all number systems on d=5
substrate, bounded by 25×25 = 625 cells.

## Filed under

  * G36-G40 (PRs #62-#68)
  * `seed/RESOLUTION_LIMIT_SPEC.md` (N_U)
  * `Lib/Math/DyadicFSM.lean` (FSM machinery)
