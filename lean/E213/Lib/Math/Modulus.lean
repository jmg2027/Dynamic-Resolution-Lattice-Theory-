import E213.Lib.Math.Modulus.HasModulus
import E213.Lib.Math.Modulus.PellHasModulus
import E213.Lib.Math.Modulus.StrongModulus
import E213.Lib.Math.Modulus.DiagonalHasModulus
import E213.Lib.Math.Modulus.DiagonalIrrelevance
import E213.Lib.Math.Modulus.Capstone

/-! Spec-as-code entry point for `E213.Lib.Math.Modulus`.

  Modulus combinators for cut-level analysis — companion to
  `Math.Real213` (the type) + `Math.Cauchy` (the convergence
  proofs).

  ## Files

  ### Core typeclass + bound lemmas

    * `HasModulus`             — `HasModulus xs N` predicate
                                 (sequence with explicit modulus
                                 of convergence) + bound lemmas
                                 (`cauchy_at_larger_N`)
    * `StrongModulus`          — strong-modulus refinement
                                 (uniform across (m, k))

  ### Concrete instances

    * `PellHasModulus`         — Pell-sequence modulus instance
    * `DiagonalHasModulus`     — diagonal sequence
                                 `(n+1, n+1)` modulus instance

  ### Lens-property results

    * `DiagonalIrrelevance`    — Note 34 §3-§4 formalisation:
                                 for injective `L.view`, the
                                 diagonal value of `L.combine`
                                 has no view effect

  ### closure-chain capstone

    * `Translation` →
      `InfoClosure` →
      `DepthCompleteness` →
      `Capstone`            — depth-modulus / information-
                                 closure / depth-completeness
                                 chain (capstone is the tip,
                                 transitively pulls in the rest).
-/
