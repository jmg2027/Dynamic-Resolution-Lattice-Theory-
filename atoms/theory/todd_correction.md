# Todd Class Correction to Screening

## The Formula

Cross-shell screening receives a curvature correction
from the Todd class of ℂP⁴:

```
σ_corrected = σ₀ - σ₀² × c₁(ℂP⁴) × α_GUT / (d²-1)
            = 7/8 - (7/8)² × 6 × α_GUT / 24
            = 7/8 - 49α/256
            = 0.8703
```

Where:
- σ₀ = 7/8 (leading order, adjoint trace)
- c₁(ℂP⁴) = d+1 = 6 (first Chern class)
- d²-1 = 24 (adjoint budget)

## Results

Applied to cross-shell only (same-shell unchanged):

| Z | Sym | ppm | Note |
|---|-----|-----|------|
| 3 | Li | +376 | ★ Z_eff error 0.0002 |
| 6 | C | +949 | ★ <1000 ppm |
| 10 | Ne | +2165 | |
| 7 | N | +4601 | |

## Physical Meaning

The Todd correction = ℂP⁴ curvature at the hinge level.
Leading screening (7/8) assumes flat space.
The correction accounts for the non-zero curvature
of the ambient projective space.

This is the SAME physics as SM_021 (Higgs embedding correction):
both arise from sub-structures embedded in ℂP⁴.

## What It Does NOT Fix

Same-shell interactions (Be, B, O pair):
these involve DIFFERENT Hodge sectors and need
sector-specific corrections (not Todd class).
