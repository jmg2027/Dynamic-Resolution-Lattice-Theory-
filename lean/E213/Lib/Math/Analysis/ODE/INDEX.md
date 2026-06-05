# Differential Equations 213 — Module Index

Blueprint: `blueprints/math/06_ode_pde_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `PicardIterate.lean` | discrete Picard `y_{n+1} = y_n + f(y_n)`; const + exp closed-form | ∅-axiom |
| `LinearODE.lean` | `y' = a` → `y0 + n·a`; `y' = y` Euler-step → `y0 · 2^n` | ∅-axiom |
| `HeatEqDiscrete.lean` | 1D periodic heat eq; maximum principle (per-step/iterated/strong-strict), comparison principle, lazy `(¼,½,¼)` stencil + checkerboard spectral-gap witness | ∅-axiom |
| `HeatEqConservation.lean` | finite-grid sum `gridSum` + cyclic-shift invariance; mass conservation `Σ heatStep = 2Σu`, `Σ lazyHeatStep = 4Σu`; summation-by-parts Dirichlet pairing `⟨u, A u⟩` | ∅-axiom |
| `HeatEqEnergyL2.lean` | pointwise L²-Jensen (convexity) bounds via POSITIVITY: `(a+b)² ≤ 2(a²+b²)`, `(a+2b+c)² ≤ 4(a²+2b²+c²)` | ∅-axiom |
| `WaveEqDiscrete.lean` | 1D periodic leapfrog wave; rest field + zero field preserved | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | ∅-axiom |
| `ODE.lean` | umbrella | — |

## 213-native paradigm

  * **ODE = Picard trajectory**: a solution is the *iteration*
    itself, not a Cauchy-limit existence proof.  At dyadic time
    grid the iterate is a polynomial in the step count.
  * **PDE = finite-grid update**: heat / wave on a length-`n`
    periodic ring is a `Nat`-valued combinatorial map; conservation
    laws are `Nat` identities (no measure-theoretic chase).
  * **No analytic completeness chase**: `cutExp`-style series
    truncate at `Grade-N` (already in Cohomology), so the
    "existence theorem" is replaced by *finite construction*.

## Honest scope

Atomic discrete schemes only.  Continuous-time `IsAntiderivative`
side hooks into existing `Lib/Math/Analysis/Integration/*` and is
not duplicated.  Picard-iteration *convergence* (Cauchy modulus
on the cut side) is a follow-up — the discrete iteration itself
is exact at every step.
