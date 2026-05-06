import E213.Physics.Basel.Bound
import E213.Physics.Basel.WhyBasel

/-! Spec-as-code entry point for `E213.Physics.Basel`.

  Basel partial-sum brackets for ζ(2) = π²/6.  Partial sum
  S(N) = Σ_{k=1..N} 1/k², with explicit lower / upper integer
  brackets used throughout the precision chain (1/α_em etc.).

  ## Files

    * `Bound`     — concrete bracket lemmas S(N₁) < ζ(2) < S(N₂)
                    at the depths needed by the physics chain.
    * `WhyBasel`  — structural witness: why ζ(2) appears in DRLT
                    (Σ 1/k² as the natural pair-resonance kernel).
-/
