import E213.Lib.Math.Analysis.ODE.NewtonFirst
import E213.Lib.Math.Analysis.ODE.NewtonSecond
import E213.Lib.Math.Analysis.ODE.ODE
import E213.Lib.Math.Analysis.ODE.PicardIterate
import E213.Lib.Math.Analysis.ODE.LinearODE
import E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
import E213.Lib.Math.Analysis.ODE.HeatEq.Conservation
import E213.Lib.Math.Analysis.ODE.HeatEq.EnergyL2
import E213.Lib.Math.Analysis.ODE.HeatEq.EnergyDecay
import E213.Lib.Math.Analysis.ODE.WaveEqDiscrete
import E213.Lib.Math.Analysis.ODE.Capstone

/-! Spec-as-code entry point for `E213.Lib.Math.Analysis.ODE`.

  Ordinary differential equations on Real213 cuts.

  ## Files

    * `ODE`           — generic ODE type + solution machinery
    * `NewtonFirst`   — Newton's first law as a degenerate ODE
                        (constant velocity)
    * `NewtonSecond`  — Newton's second law as a 2nd-order ODE
                        (linear-with-intercept derivative
                        pointwise version)
    * `PicardIterate` — Picard iteration on Real213 cuts
    * `LinearODE`     — linear ODE solution machinery
    * `HeatEq/` — discrete heat equation sub-cluster:
        - `Discrete`     — maximum principle (per-step + iterated + strict),
                           comparison principle, lazy stencil + spectral gap
        - `Conservation` — finite-grid sum `gridSum` + mass conservation
                           (`Σ heatStep = 2Σu`) + Dirichlet pairing
        - `EnergyL2`     — pointwise L²-Jensen (convexity) bounds via the
                           POSITIVITY archetype (`(a+b)² ≤ 2(a²+b²)`)
        - `EnergyDecay`  — Dirichlet energy decay `E(lazy u) ≤ 16·E(u)`
                           (the P3 capstone; `Nat`↔ℤ bridge + shift invariance)
    * `WaveEqDiscrete` — discrete wave equation
    * `Capstone`      — ODE capstone results
-/
