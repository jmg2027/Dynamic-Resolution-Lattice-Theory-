import E213.Math.Modulus.HasModulus
import E213.Math.Modulus.HasModulusBoundsExtra
import E213.Math.Modulus.PellHasModulus
import E213.Math.Modulus.StrongModulus

/-! Spec-as-code entry point for `E213.Math.Modulus`.

  Modulus combinators for cut-level analysis — companion to
  `Math.Real213` (the type) + `Math.Cauchy` (the convergence
  proofs).

  ## Files

    * `HasModulus`             — `HasModulus xs N` predicate
                                 (sequence with explicit modulus
                                 of convergence)
    * `HasModulusBoundsExtra`  — extra bound lemmas
    * `StrongModulus`          — strong-modulus refinement
                                 (uniform across (m, k))
    * `PellHasModulus`         — Pell-sequence modulus instance
-/
