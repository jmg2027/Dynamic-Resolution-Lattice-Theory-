# Ordinary Differential Equations 213

**Status**: Closed (`Analysis/ODE/`, 12 files).

## Overview

213-native ODE machinery is **Nat-discrete iteration**, not an
existence-theorem chasing analytic completeness.  An ODE `y' = f(y)`
with `y(0) = y0` is *solved by* its discrete Picard iterate
`y_{k+1} = y_k + f(y_k)`; the solution **is** the iterate, a purely
combinatorial object that closes to a closed form for the standard
right-hand sides.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Analysis/ODE/` (12 files)
- **∅-axiom status**: PURE

## Narrative

The core iterate (`PicardIterate.lean`):

```
picardIterate (y0 : Nat) (f : Nat → Nat) : Nat → Nat
  | 0     => y0
  | n + 1 => picardIterate y0 f n + f (picardIterate y0 f n)
```

Two right-hand sides collapse to closed forms, proved PURE:

- **constant RHS** `f := fun _ => c` ⟹ `y0 + n·c`
  (`picard_const`) — linear growth;
- **identity RHS** `f := fun y => y` ⟹ `y0 · 2^n`
  (`picard_exp`) — geometric growth.

These reappear as the named ODE families (`LinearODE.lean`):
`linearGrowth y0 a n = y0 + n·a = picardIterate` with constant RHS
(`linearODE_eq_picard`); `geometricGrowth y0 n = y0·2^n =
picardIterate` with identity RHS (`geometricODE_eq_picard`).

The pointwise (Real213-cut) side (`ODE.lean`): a differentiable
witness `linearWithIntercept a b` with constant derivative `a`
(`linearWithIntercept_derivative_at`), plus the elementary solutions
`y' = 0 → const` (`ode_zero_solution`), `y' = 1 → id`
(`ode_one_solution`), `y' = a/b → cutScale a b`
(`ode_rational_solution`).

Newton's laws sit in the same discrete frame: constant-velocity
position with zero acceleration (`NewtonFirst.acceleration_is_zero`,
`newton_first_law_capstone_pure`) and constant-force constant
acceleration (`NewtonSecond.constant_force_constant_acceleration`).

PDE corner (`HeatEq/`, `WaveEqDiscrete.lean`): discrete heat-step with
energy decay / max principle / conservation, and a periodic leapfrog
wave step with a constant-rest-field fixed point (`wave_const_rest`,
`wave_zero_rest`).

The capstone (`Capstone.lean`) bundles the witnesses:
`picard_witness`, `linearODE_witness`, `heat_witness`, `wave_witness`,
`total_witness`.

## Connection to other chapters

- `theory/math/numbersystems/real213.md` — the pointwise solutions are
  Real213-cut valued
- `theory/math/analysis/modulus.md` — convergence handled by the
  modulus discipline of the underlying cuts
