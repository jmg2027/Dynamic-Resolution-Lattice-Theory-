import E213.Lib.Math.Analysis.ODE.NewtonFirst
import E213.Lib.Math.Analysis.ODE.NewtonSecond
import E213.Lib.Math.Analysis.ODE.ODE
import E213.Lib.Math.Analysis.ODE.PicardIterate
import E213.Lib.Math.Analysis.ODE.LinearODE
import E213.Lib.Math.Analysis.ODE.HeatEqDiscrete
import E213.Lib.Math.Analysis.ODE.HeatEqConservation
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
    * `HeatEqDiscrete` — discrete heat equation: maximum principle
                         (per-step + iterated + strict), comparison
                         principle, lazy stencil + spectral gap
    * `HeatEqConservation` — finite-grid sum `gridSum` + mass
                         conservation (`Σ heatStep = 2Σu`)
    * `WaveEqDiscrete` — discrete wave equation
    * `Capstone`      — ODE capstone results
-/
