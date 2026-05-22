# 2D Number Grid

**Status**: Closed (4 files, capstone `G41Capstone`).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 — 2-D number grid → chapter + archive.

## Overview

The **2D number grid** organizes 213's number systems by two
orthogonal axes: vertical = Cayley-Dickson level (ℝ, ℂ, ℍ, 𝕆, ...),
horizontal = FSM-grade type.  The grid is **25 × 25** at the
level-2 `configCount` evaluation (`configCount 2 = 5²⁵`,
historically called `N_U`), with the entry at position (i, j) being
a specific number-system instance.

This is the "every number system as a grid coordinate" reading —
no number system is foundational; all are positions in the grid.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberGrid/` (4 files)
- **Capstone**: `G41Capstone.lean`
- **∅-axiom status**: PURE

| File | Purpose |
|---|---|
| `TwoDimGrid` | Grid type + (i, j) → number-system instance |
| `HorizontalAxis` | FSM-grade horizontal axis (213-native grades) |
| `FSMGradeTaxonomy` | Taxonomy of FSM grades by atomic count |
| `G41Capstone` | 25 × 25 grid master witness |

## Narrative

Classical mathematics treats ℝ, ℂ, ℍ, 𝕆 as a tower
(`vert = level`).  213 adds a second axis: horizontal grade by
FSM type (Pell, Fib, Lucas, ...).  The grid coordinate (i, j)
identifies each system:

- (0, 0) = ℝ (ZI base)
- (1, 0) = ℂ (Lipschitz)
- (2, 0) = ℍ (Cayley)
- (i, 0) = i-th CD level
- (i, j) = i-th CD level on j-th FSM-grade base

At the level-2 family evaluation (`configCount 2 = 5²⁵`), the
25×25 grid closes; positions beyond (24, 24) require a higher
family-evaluation level.  This is the geometric realization of the
algebra-tower's asymptotic behaviour (see `algebra_tower.md`).

## How to verify

```bash
cd lean
lake build E213.Lib.Math.NumberGrid
```
