# Gauge Couplings + Running

**Status**: Closed (11 files).

## Overview

DRLT gauge coupling derivations: **α_GUT = 6/(25·π²)**, α_QCD
running, gauge-coupling spectrum, photon kernel, color confinement,
Dyson structure, asymptotic freedom, **θ_QCD**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Couplings/` (11 files)
- **Umbrella**: `Couplings.lean`
- **∅-axiom status**: PURE

| Group | Files | Topic |
|---|---|---|
| Unification | `AlphaGUT`, `GUTUnification`, `RunningGap` | α_GUT = 6/(25·π²); IR/UV gap |
| α_QCD running | `AsymptoticFreedom`, `RunningGap` | β-function running |
| Spectrum | `SpectrumComplete`, `PhotonKernel`, `ClosedPropagator` | unified coupling spectrum |
| Confinement | `ColorConfinement`, `DysonStructure` | confinement + Dyson structure |
| θ-angle | `ThetaQCD` | θ_QCD < J·α⁴ falsifier |
| Triple vertex | `TripleCoupling` | triple-coupling vertex |

## Narrative

The unified coupling at the GUT scale is `α_GUT = 6/(25·π²) ≈ 0.024317`.
Numerator 6 = NS·NT (atomic dual signature); denominator 25 = d²
(squared atomic dim); π² from cup-pairing closure.

`α_QCD` running uses the standard β-function in 213-native form
(coupling = Real213-valued, β-function = Real213→Real213 with
explicit modulus per ε-δ modulus).  Asymptotic freedom = β > 0 at small
coupling (decidable bracket on the β value).

**`θ_QCD < J·α⁴`** is one of two key falsifiers in the DRLT
Validation Standard (`seed/AXIOM/08_falsifiability.md`).
Currently J = 1, α⁴ ≈ 10⁻⁹; measured θ_QCD ≤ 10⁻¹⁰ confirms
the bound, but a measured θ_QCD > 10⁻⁹ would falsify DRLT.

## Connection

- `theory/physics/foundations/atomic_constants.md` — NS·NT = 6 = α_GUT numerator
- `theory/physics/alpha_em/precision_derivation.md` — α_em (IR) from α_GUT running
- `theory/physics/symmetry/c3_chain.md` — α_3 (strong) = 1/8 = 1/dim H¹(K)
- `theory/physics/yang_mills.md` — Yang-Mills structure
