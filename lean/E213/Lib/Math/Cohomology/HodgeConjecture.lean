import E213.Lib.Math.Cohomology.HodgeConjecture.API
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing
import E213.Lib.Math.Cohomology.HodgeConjecture.Refinement
import E213.Lib.Math.Cohomology.HodgeConjecture.Structure
import E213.Lib.Math.Cohomology.HodgeConjecture.Toolkit

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.HodgeConjecture`.

  Cup-chain cohomology toolkit + surface intersection-form / signature
  results.  (The genuine ⋆⋆ = id involution lives in
  `Cohomology.Hodge.InvolutionCapstone`.)

  ## Top-level

    * `API.lean` — public surface

  ## Sub-cluster umbrellas

    * `Structure/`   — algebraic structure (Map = ⋆ as ℤ/2-bijection,
                       PoincareDuality, Ring)
    * `Pairing/`     — surface intersection forms: Hodge index /
                       Hodge–Riemann signatures on real CW surfaces
                       (T², ℙ², ℙ¹×ℙ¹, T²×T², Σ_g, products)
    * `Refinement/`  — cup-atomic generation at Δ⁴ (k=2 case-work)
    * `Toolkit/`     — Primitives, RoundTrip*
    * `Bridge/`      — statistical-mechanics + CS bridges: Ising,
                       Potts, spin glass (+ ground state), ML decoder,
                       discrete geometry
-/
