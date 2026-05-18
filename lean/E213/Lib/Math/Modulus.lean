import E213.Lib.Math.Modulus.HasModulus
import E213.Lib.Math.Modulus.PellHasModulus
import E213.Lib.Math.Modulus.StrongModulus

/-! Spec-as-code entry point for `E213.Lib.Math.Modulus`.

  Modulus combinators for cut-level analysis — companion to
  `Math.Real213` (the type) + `Math.Cauchy` (the convergence
  proofs).

  ## Files

    * `HasModulus`             — `HasModulus xs N` predicate
                                 (sequence with explicit modulus
                                 of convergence) + bound lemmas
                                 (`cauchy_at_larger_N`)
    * `StrongModulus`          — strong-modulus refinement
                                 (uniform across (m, k))
    * `PellHasModulus`         — Pell-sequence modulus instance
-/
