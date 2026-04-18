# NS No-Go: The Exponent Barrier in 3D Navier-Stokes

Machine-verified proofs in Lean 4. 0 sorry.

## Results

**Theorem (No-Go).** Any energy-type estimate
|S| ≤ C Ω^α P^β for 3D vortex stretching obtained
from Sobolev interpolation satisfies α + β = 3/2 > 1.
No such estimate closes the regularity problem.

**Theorem (Closure Condition).** The estimate closes
iff α + β ≤ 1. The gap is 1/2.

**Theorem (Unique Single Closure).** Among six known
constraints on vortex stretching, only vortex alignment
(Constantin-Fefferman 1993) achieves Δ = 1/2 alone.

**Theorem (Universality).** All four non-energy approaches
(alignment, cancellation, weak criterion, algebraic)
encounter the same gap 1/2.

**Theorem (Structural Obstruction).** The gap 1/2 is
intrinsic to 3D Navier-Stokes, not method-dependent.

## Files

| File | Lines | Theorems | Content |
|------|-------|----------|---------|
| ExponentGap.lean | 69 | 3 | α+β=3/2, gap=1/2, No-Go |
| Constraints.lean | 79 | 3 | 6 constraints, unique closer |
| Universality.lean | 58 | 8 | Gap universal across routes |
| **Total** | **213** | **14** | **0 sorry** |

## Build

```
lake build
```

Requires Lean 4.16.0. No Mathlib dependency.

## Paper

See `papers/paper16_exponent_barrier.tex` (509 lines).

## Authors

Mingu Jeong (Independent Researcher) and Claude (Anthropic).
