import E213.Kernel.Tactic.Fin213
import E213.Kernel.Tactic.Mod213
import E213.Kernel.Tactic.Nat213
import E213.Kernel.Tactic.Omega213
import E213.Kernel.Tactic.Pow213
import E213.Kernel.Tactic.QuadNorm
import E213.Kernel.Tactic.Test.QuadNormTest

/-! Spec-as-code entry point for `E213.Kernel.Tactic`.

  213-native tactics at the Kernel layer — replacements for
  Lean's `omega` / `simp` that bring zero hidden axioms.

  ## Files

    * `Nat213`     — `Nat`-arithmetic helpers (substitutes for
                     `omega` in many leaf-level proofs)
    * `Mod213`     — modular-arithmetic decisions
    * `Fin213`     — `Fin n` index manipulation
    * `Pow213`     — power / exponent decisions
    * `Omega213`   — bracket-only `omega` replacement
    * `QuadNorm`   — `quad_norm` macro for Diophantus-style
                     polynomial-identity goals
    * `Test/QuadNormTest` — `quad_norm` regression tests
-/
