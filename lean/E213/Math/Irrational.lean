import E213.Math.Irrational.Sqrt2
import E213.Math.Irrational.Sqrt2Cut
import E213.Math.Irrational.Sqrt2KernelFree
import E213.Math.Irrational.Sqrt2Pure
import E213.Math.Irrational.Sqrt3Pure
import E213.Math.Irrational.Sqrt5Pure

/-! Spec-as-code entry point for `E213.Math.Irrational`.

  213-native irrationality proofs without ZFC — using
  `Real213` cuts + Pell-like algebraic invariants.

  ## Files

    * `Sqrt2`           — main √2 irrationality result
    * `Sqrt2Cut`        — cut-form variant (RealCut at √2)
    * `Sqrt2Pure`       — pure-Nat variant (avoids cut)
    * `Sqrt2KernelFree` — Kernel/Tactic-free variant
                          (descent without `omega`)
    * `Sqrt3Pure`       — √3 irrationality (pure-Nat)
    * `Sqrt5Pure`       — √5 irrationality (pure-Nat)
-/
