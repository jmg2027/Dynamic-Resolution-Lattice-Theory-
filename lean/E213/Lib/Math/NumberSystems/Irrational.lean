import E213.Lib.Math.NumberSystems.Irrational.SqrtPure
import E213.Lib.Math.NumberSystems.Irrational.Sqrt2Cut
import E213.Lib.Math.NumberSystems.Irrational.Sqrt2KernelFree

/-! Spec-as-code entry point for `E213.Lib.Math.NumberSystems.Irrational`.

  213-native irrationality proofs without ZFC — using
  `Real213` cuts + Pell-like algebraic invariants.

  ## Files

    * `Sqrt2KernelFree` — main √2 irrationality (PURE / ∅-axiom).
                          Descent without `omega`, kernel-free.
                          Supersedes the deleted `Sqrt2.lean`
                          (DIRTY [propext, Quot.sound] via omega).
    * `Sqrt2Cut`        — cut-form variant (RealCut at √2)
    * `Sqrt2Pure`       — pure-Nat variant (avoids cut)
    * `Sqrt3Pure`       — √3 irrationality (pure-Nat)
    * `Sqrt5Pure`       — √5 irrationality (pure-Nat)
-/
