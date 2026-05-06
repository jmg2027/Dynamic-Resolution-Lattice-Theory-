import E213.Lib.Math.Analysis.ODE.NewtonFirst
import E213.Lib.Math.Analysis.ODE.NewtonSecond
import E213.Lib.Math.Analysis.ODE.ODE

/-! Spec-as-code entry point for `E213.Lib.Math.Analysis.ODE`.

  Ordinary differential equations on Real213 cuts.

  ## Files

    * `ODE`           — generic ODE type + solution machinery
    * `NewtonFirst`   — Newton's first law as a degenerate ODE
                        (constant velocity)
    * `NewtonSecond`  — Newton's second law as a 2nd-order ODE
                        (linear-with-intercept derivative
                        pointwise version)
-/
